use std::{
    array,
    borrow::{Borrow, BorrowMut},
};

use openvm_circuit::arch::{
    AdapterAirContext, AdapterRuntimeContext, MinimalInstruction, Result, VmAdapterInterface,
    VmCoreAir, VmCoreChip,
};
use openvm_circuit_primitives::{
    bitwise_op_lookup::{BitwiseOperationLookupBus, SharedBitwiseOperationLookupChip},
    utils::not,
    var_range::{SharedVariableRangeCheckerChip, VariableRangeCheckerBus},
};
use openvm_circuit_primitives_derive::AlignedBorrow;
use openvm_instructions::{instruction::Instruction, LocalOpcode};
use openvm_rv32im_transpiler::ShiftOpcode;
use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{AirBuilder, BaseAir},
    p3_field::{Field, FieldAlgebra, PrimeField32},
    rap::BaseAirWithPublicValues,
};
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use serde_big_array::BigArray;
use strum::IntoEnumIterator;

#[repr(C)]
#[derive(AlignedBorrow, Clone, Copy, Debug)]
pub struct ShiftCoreCols<T, const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    pub a: [T; NUM_LIMBS],
    pub b: [T; NUM_LIMBS],
    pub c: [T; NUM_LIMBS],

    pub opcode_sll_flag: T,
    pub opcode_srl_flag: T,
    pub opcode_sra_flag: T,

    // bit_multiplier = 2^bit_shift
    pub bit_multiplier_left: T,
    pub bit_multiplier_right: T,

    // Sign of x for SRA
    pub b_sign: T,

    // Boolean columns that are 1 exactly at the index of the bit/limb shift amount
    pub bit_shift_marker: [T; LIMB_BITS],
    pub limb_shift_marker: [T; NUM_LIMBS],

    // Part of each x[i] that gets bit shifted to the next limb
    pub bit_shift_carry: [T; NUM_LIMBS],
}

#[derive(Copy, Clone, Debug)]
pub struct ShiftCoreAir<const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    pub bitwise_lookup_bus: BitwiseOperationLookupBus,
    pub range_bus: VariableRangeCheckerBus,
    pub offset: usize,
}

impl<F: Field, const NUM_LIMBS: usize, const LIMB_BITS: usize> BaseAir<F>
    for ShiftCoreAir<NUM_LIMBS, LIMB_BITS>
{
    fn width(&self) -> usize {
        ShiftCoreCols::<F, NUM_LIMBS, LIMB_BITS>::width()
    }
}
impl<F: Field, const NUM_LIMBS: usize, const LIMB_BITS: usize> BaseAirWithPublicValues<F>
    for ShiftCoreAir<NUM_LIMBS, LIMB_BITS>
{
}

impl<AB, I, const NUM_LIMBS: usize, const LIMB_BITS: usize> VmCoreAir<AB, I>
    for ShiftCoreAir<NUM_LIMBS, LIMB_BITS>
where
    AB: InteractionBuilder,
    I: VmAdapterInterface<AB::Expr>,
    I::Reads: From<[[AB::Expr; NUM_LIMBS]; 2]>,
    I::Writes: From<[[AB::Expr; NUM_LIMBS]; 1]>,
    I::ProcessedInstruction: From<MinimalInstruction<AB::Expr>>,
{
    fn eval(
        &self,
        builder: &mut AB,
        local_core: &[AB::Var],
        _from_pc: AB::Var,
    ) -> AdapterAirContext<AB::Expr, I> {
        let cols: &ShiftCoreCols<_, NUM_LIMBS, LIMB_BITS> = local_core.borrow();
        let flags = [
            cols.opcode_sll_flag,
            cols.opcode_srl_flag,
            cols.opcode_sra_flag,
        ];

        let is_valid = flags.iter().fold(AB::Expr::ZERO, |acc, &flag| {
            builder.assert_bool(flag);
            acc + flag.into()
        });
        builder.assert_bool(is_valid.clone());

        let a = &cols.a;
        let b = &cols.b;
        let c = &cols.c;
        let right_shift = cols.opcode_srl_flag + cols.opcode_sra_flag;

        // Constrain that bit_shift, bit_multiplier are correct, i.e. that bit_multiplier =
        // 1 << bit_shift. Because the sum of all bit_shift_marker[i] is constrained to be
        // 1, bit_shift is guaranteed to be in range.
        let mut bit_marker_sum = AB::Expr::ZERO;
        let mut bit_shift = AB::Expr::ZERO;

        for i in 0..LIMB_BITS {
            builder.assert_bool(cols.bit_shift_marker[i]);
            bit_marker_sum += cols.bit_shift_marker[i].into();
            bit_shift += AB::Expr::from_canonical_usize(i) * cols.bit_shift_marker[i];

            let mut when_bit_shift = builder.when(cols.bit_shift_marker[i]);
            when_bit_shift.assert_eq(
                cols.bit_multiplier_left,
                AB::Expr::from_canonical_usize(1 << i) * cols.opcode_sll_flag,
            );
            when_bit_shift.assert_eq(
                cols.bit_multiplier_right,
                AB::Expr::from_canonical_usize(1 << i) * right_shift.clone(),
            );
        }
        builder.when(is_valid.clone()).assert_one(bit_marker_sum);

        // Check that a[i] = b[i] <</>> c[i] both on the bit and limb shift level if c <
        // NUM_LIMBS * LIMB_BITS.
        let mut limb_marker_sum = AB::Expr::ZERO;
        let mut limb_shift = AB::Expr::ZERO;
        for i in 0..NUM_LIMBS {
            builder.assert_bool(cols.limb_shift_marker[i]);
            limb_marker_sum += cols.limb_shift_marker[i].into();
            limb_shift += AB::Expr::from_canonical_usize(i) * cols.limb_shift_marker[i];

            let mut when_limb_shift = builder.when(cols.limb_shift_marker[i]);

            for j in 0..NUM_LIMBS {
                // SLL constraints
                if j < i {
                    when_limb_shift.assert_zero(a[j] * cols.opcode_sll_flag);
                } else {
                    let expected_a_left = if j - i == 0 {
                        AB::Expr::ZERO
                    } else {
                        cols.bit_shift_carry[j - i - 1].into() * cols.opcode_sll_flag
                    } + b[j - i] * cols.bit_multiplier_left
                        - AB::Expr::from_canonical_usize(1 << LIMB_BITS)
                            * cols.bit_shift_carry[j - i]
                            * cols.opcode_sll_flag;
                    when_limb_shift.assert_eq(a[j] * cols.opcode_sll_flag, expected_a_left);
                }

                // SRL and SRA constraints. Combining with above would require an additional column.
                if j + i > NUM_LIMBS - 1 {
                    when_limb_shift.assert_eq(
                        a[j] * right_shift.clone(),
                        cols.b_sign * AB::F::from_canonical_usize((1 << LIMB_BITS) - 1),
                    );
                } else {
                    let expected_a_right = if j + i == NUM_LIMBS - 1 {
                        cols.b_sign * (cols.bit_multiplier_right - AB::F::ONE)
                    } else {
                        cols.bit_shift_carry[j + i + 1].into() * right_shift.clone()
                    } * AB::F::from_canonical_usize(1 << LIMB_BITS)
                        + right_shift.clone() * (b[j + i] - cols.bit_shift_carry[j + i]);
                    when_limb_shift.assert_eq(a[j] * cols.bit_multiplier_right, expected_a_right);
                }
            }
        }
        builder.when(is_valid.clone()).assert_one(limb_marker_sum);

        // Check that bit_shift and limb_shift are correct.
        let num_bits = AB::F::from_canonical_usize(NUM_LIMBS * LIMB_BITS);
        self.range_bus
            .range_check(
                (c[0] - limb_shift * AB::F::from_canonical_usize(LIMB_BITS) - bit_shift.clone())
                    * num_bits.inverse(),
                LIMB_BITS - ((NUM_LIMBS * LIMB_BITS) as u32).ilog2() as usize,
            )
            .eval(builder, is_valid.clone());

        // Check b_sign & b[NUM_LIMBS - 1] == b_sign using XOR
        builder.assert_bool(cols.b_sign);
        builder
            .when(not(cols.opcode_sra_flag))
            .assert_zero(cols.b_sign);

        let mask = AB::F::from_canonical_u32(1 << (LIMB_BITS - 1));
        let b_sign_shifted = cols.b_sign * mask;
        self.bitwise_lookup_bus
            .send_xor(
                b[NUM_LIMBS - 1],
                mask,
                b[NUM_LIMBS - 1] + mask - (AB::Expr::from_canonical_u32(2) * b_sign_shifted),
            )
            .eval(builder, cols.opcode_sra_flag);

        for i in 0..(NUM_LIMBS / 2) {
            self.bitwise_lookup_bus
                .send_range(a[i * 2], a[i * 2 + 1])
                .eval(builder, is_valid.clone());
        }

        for carry in cols.bit_shift_carry {
            self.range_bus
                .send(carry, bit_shift.clone())
                .eval(builder, is_valid.clone());
        }

        let expected_opcode = VmCoreAir::<AB, I>::expr_to_global_expr(
            self,
            flags
                .iter()
                .zip(ShiftOpcode::iter())
                .fold(AB::Expr::ZERO, |acc, (flag, opcode)| {
                    acc + (*flag).into() * AB::Expr::from_canonical_u8(opcode as u8)
                }),
        );

        AdapterAirContext {
            to_pc: None,
            reads: [cols.b.map(Into::into), cols.c.map(Into::into)].into(),
            writes: [cols.a.map(Into::into)].into(),
            instruction: MinimalInstruction {
                is_valid,
                opcode: expected_opcode,
            }
            .into(),
        }
    }

    fn start_offset(&self) -> usize {
        self.offset
    }
}

#[repr(C)]
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "T: Serialize + DeserializeOwned")]
pub struct ShiftCoreRecord<T, const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    #[serde(with = "BigArray")]
    pub a: [T; NUM_LIMBS],
    #[serde(with = "BigArray")]
    pub b: [T; NUM_LIMBS],
    #[serde(with = "BigArray")]
    pub c: [T; NUM_LIMBS],
    pub b_sign: T,
    #[serde(with = "BigArray")]
    pub bit_shift_carry: [u32; NUM_LIMBS],
    pub bit_shift: usize,
    pub limb_shift: usize,
    pub opcode: ShiftOpcode,
}

pub struct ShiftCoreChip<const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    pub air: ShiftCoreAir<NUM_LIMBS, LIMB_BITS>,
    pub bitwise_lookup_chip: SharedBitwiseOperationLookupChip<LIMB_BITS>,
    pub range_checker_chip: SharedVariableRangeCheckerChip,
}

impl<const NUM_LIMBS: usize, const LIMB_BITS: usize> ShiftCoreChip<NUM_LIMBS, LIMB_BITS> {
    pub fn new(
        bitwise_lookup_chip: SharedBitwiseOperationLookupChip<LIMB_BITS>,
        range_checker_chip: SharedVariableRangeCheckerChip,
        offset: usize,
    ) -> Self {
        assert_eq!(NUM_LIMBS % 2, 0, "Number of limbs must be divisible by 2");
        Self {
            air: ShiftCoreAir {
                bitwise_lookup_bus: bitwise_lookup_chip.bus(),
                range_bus: range_checker_chip.bus(),
                offset,
            },
            bitwise_lookup_chip,
            range_checker_chip,
        }
    }
}

impl<F: PrimeField32, I: VmAdapterInterface<F>, const NUM_LIMBS: usize, const LIMB_BITS: usize>
    VmCoreChip<F, I> for ShiftCoreChip<NUM_LIMBS, LIMB_BITS>
where
    I::Reads: Into<[[F; NUM_LIMBS]; 2]>,
    I::Writes: From<[[F; NUM_LIMBS]; 1]>,
{
    type Record = ShiftCoreRecord<F, NUM_LIMBS, LIMB_BITS>;
    type Air = ShiftCoreAir<NUM_LIMBS, LIMB_BITS>;

    #[allow(clippy::type_complexity)]
    fn execute_instruction(
        &self,
        instruction: &Instruction<F>,
        _from_pc: u32,
        reads: I::Reads,
    ) -> Result<(AdapterRuntimeContext<F, I>, Self::Record)> {
        let Instruction { opcode, .. } = instruction;
        let shift_opcode = ShiftOpcode::from_usize(opcode.local_opcode_idx(self.air.offset));

        let data: [[F; NUM_LIMBS]; 2] = reads.into();
        let b = data[0].map(|x| x.as_canonical_u32());
        let c = data[1].map(|y| y.as_canonical_u32());
        let (a, limb_shift, bit_shift) = run_shift::<NUM_LIMBS, LIMB_BITS>(shift_opcode, &b, &c);

        let bit_shift_carry = array::from_fn(|i| match shift_opcode {
            ShiftOpcode::SLL => b[i] >> (LIMB_BITS - bit_shift),
            _ => b[i] % (1 << bit_shift),
        });

        let mut b_sign = 0;
        if shift_opcode == ShiftOpcode::SRA {
            b_sign = b[NUM_LIMBS - 1] >> (LIMB_BITS - 1);
            self.bitwise_lookup_chip
                .request_xor(b[NUM_LIMBS - 1], 1 << (LIMB_BITS - 1));
        }

        for i in 0..(NUM_LIMBS / 2) {
            self.bitwise_lookup_chip
                .request_range(a[i * 2], a[i * 2 + 1]);
        }

        let output = AdapterRuntimeContext::without_pc([a.map(F::from_canonical_u32)]);
        let record = ShiftCoreRecord {
            opcode: shift_opcode,
            a: a.map(F::from_canonical_u32),
            b: data[0],
            c: data[1],
            bit_shift_carry,
            bit_shift,
            limb_shift,
            b_sign: F::from_canonical_u32(b_sign),
        };

        Ok((output, record))
    }

    fn get_opcode_name(&self, opcode: usize) -> String {
        format!("{:?}", ShiftOpcode::from_usize(opcode - self.air.offset))
    }

    fn generate_trace_row(&self, row_slice: &mut [F], record: Self::Record) {
        for carry_val in record.bit_shift_carry {
            self.range_checker_chip
                .add_count(carry_val, record.bit_shift);
        }

        let num_bits_log = (NUM_LIMBS * LIMB_BITS).ilog2();
        self.range_checker_chip.add_count(
            (((record.c[0].as_canonical_u32() as usize)
                - record.bit_shift
                - record.limb_shift * LIMB_BITS)
                >> num_bits_log) as u32,
            LIMB_BITS - num_bits_log as usize,
        );

        let row_slice: &mut ShiftCoreCols<_, NUM_LIMBS, LIMB_BITS> = row_slice.borrow_mut();
        row_slice.a = record.a;
        row_slice.b = record.b;
        row_slice.c = record.c;
        row_slice.bit_multiplier_left = match record.opcode {
            ShiftOpcode::SLL => F::from_canonical_usize(1 << record.bit_shift),
            _ => F::ZERO,
        };
        row_slice.bit_multiplier_right = match record.opcode {
            ShiftOpcode::SLL => F::ZERO,
            _ => F::from_canonical_usize(1 << record.bit_shift),
        };
        row_slice.b_sign = record.b_sign;
        row_slice.bit_shift_marker = array::from_fn(|i| F::from_bool(i == record.bit_shift));
        row_slice.limb_shift_marker = array::from_fn(|i| F::from_bool(i == record.limb_shift));
        row_slice.bit_shift_carry = record.bit_shift_carry.map(F::from_canonical_u32);
        row_slice.opcode_sll_flag = F::from_bool(record.opcode == ShiftOpcode::SLL);
        row_slice.opcode_srl_flag = F::from_bool(record.opcode == ShiftOpcode::SRL);
        row_slice.opcode_sra_flag = F::from_bool(record.opcode == ShiftOpcode::SRA);
    }

    fn air(&self) -> &Self::Air {
        &self.air
    }
}

pub(super) fn run_shift<const NUM_LIMBS: usize, const LIMB_BITS: usize>(
    opcode: ShiftOpcode,
    x: &[u32; NUM_LIMBS],
    y: &[u32; NUM_LIMBS],
) -> ([u32; NUM_LIMBS], usize, usize) {
    match opcode {
        ShiftOpcode::SLL => run_shift_left::<NUM_LIMBS, LIMB_BITS>(x, y),
        ShiftOpcode::SRL => run_shift_right::<NUM_LIMBS, LIMB_BITS>(x, y, true),
        ShiftOpcode::SRA => run_shift_right::<NUM_LIMBS, LIMB_BITS>(x, y, false),
    }
}

fn run_shift_left<const NUM_LIMBS: usize, const LIMB_BITS: usize>(
    x: &[u32; NUM_LIMBS],
    y: &[u32; NUM_LIMBS],
) -> ([u32; NUM_LIMBS], usize, usize) {
    let mut result = [0u32; NUM_LIMBS];

    let (limb_shift, bit_shift) = get_shift::<NUM_LIMBS, LIMB_BITS>(y);

    for i in limb_shift..NUM_LIMBS {
        result[i] = if i > limb_shift {
            ((x[i - limb_shift] << bit_shift) + (x[i - limb_shift - 1] >> (LIMB_BITS - bit_shift)))
                % (1 << LIMB_BITS)
        } else {
            (x[i - limb_shift] << bit_shift) % (1 << LIMB_BITS)
        };
    }
    (result, limb_shift, bit_shift)
}

fn run_shift_right<const NUM_LIMBS: usize, const LIMB_BITS: usize>(
    x: &[u32; NUM_LIMBS],
    y: &[u32; NUM_LIMBS],
    logical: bool,
) -> ([u32; NUM_LIMBS], usize, usize) {
    let fill = if logical {
        0
    } else {
        ((1 << LIMB_BITS) - 1) * (x[NUM_LIMBS - 1] >> (LIMB_BITS - 1))
    };
    let mut result = [fill; NUM_LIMBS];

    let (limb_shift, bit_shift) = get_shift::<NUM_LIMBS, LIMB_BITS>(y);

    for i in 0..(NUM_LIMBS - limb_shift) {
        result[i] = if i + limb_shift + 1 < NUM_LIMBS {
            ((x[i + limb_shift] >> bit_shift) + (x[i + limb_shift + 1] << (LIMB_BITS - bit_shift)))
                % (1 << LIMB_BITS)
        } else {
            ((x[i + limb_shift] >> bit_shift) + (fill << (LIMB_BITS - bit_shift)))
                % (1 << LIMB_BITS)
        }
    }
    (result, limb_shift, bit_shift)
}

fn get_shift<const NUM_LIMBS: usize, const LIMB_BITS: usize>(y: &[u32]) -> (usize, usize) {
    // We assume `NUM_LIMBS * LIMB_BITS <= 2^LIMB_BITS` so so the shift is defined
    // entirely in y[0].
    let shift = (y[0] as usize) % (NUM_LIMBS * LIMB_BITS);
    (shift / LIMB_BITS, shift % LIMB_BITS)
}
