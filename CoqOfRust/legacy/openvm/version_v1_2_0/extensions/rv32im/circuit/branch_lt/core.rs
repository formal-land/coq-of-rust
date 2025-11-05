use std::{
    array,
    borrow::{Borrow, BorrowMut},
};

use openvm_circuit::arch::{
    AdapterAirContext, AdapterRuntimeContext, ImmInstruction, Result, VmAdapterInterface,
    VmCoreAir, VmCoreChip,
};
use openvm_circuit_primitives::{
    bitwise_op_lookup::{BitwiseOperationLookupBus, SharedBitwiseOperationLookupChip},
    utils::not,
};
use openvm_circuit_primitives_derive::AlignedBorrow;
use openvm_instructions::{instruction::Instruction, program::DEFAULT_PC_STEP, LocalOpcode};
use openvm_rv32im_transpiler::BranchLessThanOpcode;
use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{AirBuilder, BaseAir},
    p3_field::{Field, FieldAlgebra, PrimeField32},
    rap::BaseAirWithPublicValues,
};
use serde::{Deserialize, Serialize};
use serde_big_array::BigArray;
use strum::IntoEnumIterator;

#[repr(C)]
#[derive(AlignedBorrow)]
pub struct BranchLessThanCoreCols<T, const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    pub a: [T; NUM_LIMBS],
    pub b: [T; NUM_LIMBS],

    // Boolean result of a op b. Should branch if and only if cmp_result = 1.
    pub cmp_result: T,
    pub imm: T,

    pub opcode_blt_flag: T,
    pub opcode_bltu_flag: T,
    pub opcode_bge_flag: T,
    pub opcode_bgeu_flag: T,

    // Most significant limb of a and b respectively as a field element, will be range
    // checked to be within [-128, 127) if signed and [0, 256) if unsigned.
    pub a_msb_f: T,
    pub b_msb_f: T,

    // 1 if a < b, 0 otherwise.
    pub cmp_lt: T,

    // 1 at the most significant index i such that a[i] != b[i], otherwise 0. If such
    // an i exists, diff_val = b[i] - a[i].
    pub diff_marker: [T; NUM_LIMBS],
    pub diff_val: T,
}

#[derive(Copy, Clone, Debug)]
pub struct BranchLessThanCoreAir<const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    pub bus: BitwiseOperationLookupBus,
    offset: usize,
}

impl<F: Field, const NUM_LIMBS: usize, const LIMB_BITS: usize> BaseAir<F>
    for BranchLessThanCoreAir<NUM_LIMBS, LIMB_BITS>
{
    fn width(&self) -> usize {
        BranchLessThanCoreCols::<F, NUM_LIMBS, LIMB_BITS>::width()
    }
}
impl<F: Field, const NUM_LIMBS: usize, const LIMB_BITS: usize> BaseAirWithPublicValues<F>
    for BranchLessThanCoreAir<NUM_LIMBS, LIMB_BITS>
{
}

impl<AB, I, const NUM_LIMBS: usize, const LIMB_BITS: usize> VmCoreAir<AB, I>
    for BranchLessThanCoreAir<NUM_LIMBS, LIMB_BITS>
where
    AB: InteractionBuilder,
    I: VmAdapterInterface<AB::Expr>,
    I::Reads: From<[[AB::Expr; NUM_LIMBS]; 2]>,
    I::Writes: Default,
    I::ProcessedInstruction: From<ImmInstruction<AB::Expr>>,
{
    fn eval(
        &self,
        builder: &mut AB,
        local_core: &[AB::Var],
        from_pc: AB::Var,
    ) -> AdapterAirContext<AB::Expr, I> {
        let cols: &BranchLessThanCoreCols<_, NUM_LIMBS, LIMB_BITS> = local_core.borrow();
        let flags = [
            cols.opcode_blt_flag,
            cols.opcode_bltu_flag,
            cols.opcode_bge_flag,
            cols.opcode_bgeu_flag,
        ];

        let is_valid = flags.iter().fold(AB::Expr::ZERO, |acc, &flag| {
            builder.assert_bool(flag);
            acc + flag.into()
        });
        builder.assert_bool(is_valid.clone());
        builder.assert_bool(cols.cmp_result);

        let lt = cols.opcode_blt_flag + cols.opcode_bltu_flag;
        let ge = cols.opcode_bge_flag + cols.opcode_bgeu_flag;
        let signed = cols.opcode_blt_flag + cols.opcode_bge_flag;
        builder.assert_eq(
            cols.cmp_lt,
            cols.cmp_result * lt.clone() + not(cols.cmp_result) * ge.clone(),
        );

        let a = &cols.a;
        let b = &cols.b;
        let marker = &cols.diff_marker;
        let mut prefix_sum = AB::Expr::ZERO;

        // Check if a_msb_f and b_msb_f are signed values of a[NUM_LIMBS - 1] and b[NUM_LIMBS - 1]
        // in prime field F.
        let a_diff = a[NUM_LIMBS - 1] - cols.a_msb_f;
        let b_diff = b[NUM_LIMBS - 1] - cols.b_msb_f;
        builder
            .assert_zero(a_diff.clone() * (AB::Expr::from_canonical_u32(1 << LIMB_BITS) - a_diff));
        builder
            .assert_zero(b_diff.clone() * (AB::Expr::from_canonical_u32(1 << LIMB_BITS) - b_diff));

        for i in (0..NUM_LIMBS).rev() {
            let diff = (if i == NUM_LIMBS - 1 {
                cols.b_msb_f - cols.a_msb_f
            } else {
                b[i] - a[i]
            }) * (AB::Expr::from_canonical_u8(2) * cols.cmp_lt - AB::Expr::ONE);
            prefix_sum += marker[i].into();
            builder.assert_bool(marker[i]);
            builder.assert_zero(not::<AB::Expr>(prefix_sum.clone()) * diff.clone());
            builder.when(marker[i]).assert_eq(cols.diff_val, diff);
        }
        // - If x != y, then prefix_sum = 1 so marker[i] must be 1 iff i is the first index where
        //   diff != 0. Constrains that diff == diff_val where diff_val is non-zero.
        // - If x == y, then prefix_sum = 0 and cmp_lt = 0. Here, prefix_sum cannot be 1 because all
        //   diff are zero, making diff == diff_val fails.

        builder.assert_bool(prefix_sum.clone());
        builder
            .when(not::<AB::Expr>(prefix_sum.clone()))
            .assert_zero(cols.cmp_lt);

        // Check if a_msb_f and b_msb_f are in [-128, 127) if signed, [0, 256) if unsigned.
        self.bus
            .send_range(
                cols.a_msb_f + AB::Expr::from_canonical_u32(1 << (LIMB_BITS - 1)) * signed.clone(),
                cols.b_msb_f + AB::Expr::from_canonical_u32(1 << (LIMB_BITS - 1)) * signed.clone(),
            )
            .eval(builder, is_valid.clone());

        // Range check to ensure diff_val is non-zero.
        self.bus
            .send_range(cols.diff_val - AB::Expr::ONE, AB::F::ZERO)
            .eval(builder, prefix_sum);

        let expected_opcode = flags
            .iter()
            .zip(BranchLessThanOpcode::iter())
            .fold(AB::Expr::ZERO, |acc, (flag, opcode)| {
                acc + (*flag).into() * AB::Expr::from_canonical_u8(opcode as u8)
            })
            + AB::Expr::from_canonical_usize(self.offset);

        let to_pc = from_pc
            + cols.cmp_result * cols.imm
            + not(cols.cmp_result) * AB::Expr::from_canonical_u32(DEFAULT_PC_STEP);

        AdapterAirContext {
            to_pc: Some(to_pc),
            reads: [cols.a.map(Into::into), cols.b.map(Into::into)].into(),
            writes: Default::default(),
            instruction: ImmInstruction {
                is_valid,
                opcode: expected_opcode,
                immediate: cols.imm.into(),
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
pub struct BranchLessThanCoreRecord<T, const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    #[serde(with = "BigArray")]
    pub a: [T; NUM_LIMBS],
    #[serde(with = "BigArray")]
    pub b: [T; NUM_LIMBS],
    pub cmp_result: T,
    pub cmp_lt: T,
    pub imm: T,
    pub a_msb_f: T,
    pub b_msb_f: T,
    pub diff_val: T,
    pub diff_idx: usize,
    pub opcode: BranchLessThanOpcode,
}

pub struct BranchLessThanCoreChip<const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    pub air: BranchLessThanCoreAir<NUM_LIMBS, LIMB_BITS>,
    pub bitwise_lookup_chip: SharedBitwiseOperationLookupChip<LIMB_BITS>,
}

impl<const NUM_LIMBS: usize, const LIMB_BITS: usize> BranchLessThanCoreChip<NUM_LIMBS, LIMB_BITS> {
    pub fn new(
        bitwise_lookup_chip: SharedBitwiseOperationLookupChip<LIMB_BITS>,
        offset: usize,
    ) -> Self {
        Self {
            air: BranchLessThanCoreAir {
                bus: bitwise_lookup_chip.bus(),
                offset,
            },
            bitwise_lookup_chip,
        }
    }
}

impl<F: PrimeField32, I: VmAdapterInterface<F>, const NUM_LIMBS: usize, const LIMB_BITS: usize>
    VmCoreChip<F, I> for BranchLessThanCoreChip<NUM_LIMBS, LIMB_BITS>
where
    I::Reads: Into<[[F; NUM_LIMBS]; 2]>,
    I::Writes: Default,
{
    type Record = BranchLessThanCoreRecord<F, NUM_LIMBS, LIMB_BITS>;
    type Air = BranchLessThanCoreAir<NUM_LIMBS, LIMB_BITS>;

    #[allow(clippy::type_complexity)]
    fn execute_instruction(
        &self,
        instruction: &Instruction<F>,
        from_pc: u32,
        reads: I::Reads,
    ) -> Result<(AdapterRuntimeContext<F, I>, Self::Record)> {
        let Instruction { opcode, c: imm, .. } = *instruction;
        let blt_opcode = BranchLessThanOpcode::from_usize(opcode.local_opcode_idx(self.air.offset));

        let data: [[F; NUM_LIMBS]; 2] = reads.into();
        let a = data[0].map(|x| x.as_canonical_u32());
        let b = data[1].map(|y| y.as_canonical_u32());
        let (cmp_result, diff_idx, a_sign, b_sign) =
            run_cmp::<NUM_LIMBS, LIMB_BITS>(blt_opcode, &a, &b);

        let signed = matches!(
            blt_opcode,
            BranchLessThanOpcode::BLT | BranchLessThanOpcode::BGE
        );
        let ge_opcode = matches!(
            blt_opcode,
            BranchLessThanOpcode::BGE | BranchLessThanOpcode::BGEU
        );
        let cmp_lt = cmp_result ^ ge_opcode;

        // We range check (a_msb_f + 128) and (b_msb_f + 128) if signed,
        // a_msb_f and b_msb_f if not
        let (a_msb_f, a_msb_range) = if a_sign {
            (
                -F::from_canonical_u32((1 << LIMB_BITS) - a[NUM_LIMBS - 1]),
                a[NUM_LIMBS - 1] - (1 << (LIMB_BITS - 1)),
            )
        } else {
            (
                F::from_canonical_u32(a[NUM_LIMBS - 1]),
                a[NUM_LIMBS - 1] + ((signed as u32) << (LIMB_BITS - 1)),
            )
        };
        let (b_msb_f, b_msb_range) = if b_sign {
            (
                -F::from_canonical_u32((1 << LIMB_BITS) - b[NUM_LIMBS - 1]),
                b[NUM_LIMBS - 1] - (1 << (LIMB_BITS - 1)),
            )
        } else {
            (
                F::from_canonical_u32(b[NUM_LIMBS - 1]),
                b[NUM_LIMBS - 1] + ((signed as u32) << (LIMB_BITS - 1)),
            )
        };
        self.bitwise_lookup_chip
            .request_range(a_msb_range, b_msb_range);

        let diff_val = if diff_idx == NUM_LIMBS {
            0
        } else if diff_idx == (NUM_LIMBS - 1) {
            if cmp_lt {
                b_msb_f - a_msb_f
            } else {
                a_msb_f - b_msb_f
            }
            .as_canonical_u32()
        } else if cmp_lt {
            b[diff_idx] - a[diff_idx]
        } else {
            a[diff_idx] - b[diff_idx]
        };

        if diff_idx != NUM_LIMBS {
            self.bitwise_lookup_chip.request_range(diff_val - 1, 0);
        }

        let output = AdapterRuntimeContext {
            to_pc: cmp_result.then_some((F::from_canonical_u32(from_pc) + imm).as_canonical_u32()),
            writes: Default::default(),
        };
        let record = BranchLessThanCoreRecord {
            opcode: blt_opcode,
            a: data[0],
            b: data[1],
            cmp_result: F::from_bool(cmp_result),
            cmp_lt: F::from_bool(cmp_lt),
            imm,
            a_msb_f,
            b_msb_f,
            diff_val: F::from_canonical_u32(diff_val),
            diff_idx,
        };

        Ok((output, record))
    }

    fn get_opcode_name(&self, opcode: usize) -> String {
        format!(
            "{:?}",
            BranchLessThanOpcode::from_usize(opcode - self.air.offset)
        )
    }

    fn generate_trace_row(&self, row_slice: &mut [F], record: Self::Record) {
        let row_slice: &mut BranchLessThanCoreCols<_, NUM_LIMBS, LIMB_BITS> =
            row_slice.borrow_mut();
        row_slice.a = record.a;
        row_slice.b = record.b;
        row_slice.cmp_result = record.cmp_result;
        row_slice.cmp_lt = record.cmp_lt;
        row_slice.imm = record.imm;
        row_slice.a_msb_f = record.a_msb_f;
        row_slice.b_msb_f = record.b_msb_f;
        row_slice.diff_marker = array::from_fn(|i| F::from_bool(i == record.diff_idx));
        row_slice.diff_val = record.diff_val;
        row_slice.opcode_blt_flag = F::from_bool(record.opcode == BranchLessThanOpcode::BLT);
        row_slice.opcode_bltu_flag = F::from_bool(record.opcode == BranchLessThanOpcode::BLTU);
        row_slice.opcode_bge_flag = F::from_bool(record.opcode == BranchLessThanOpcode::BGE);
        row_slice.opcode_bgeu_flag = F::from_bool(record.opcode == BranchLessThanOpcode::BGEU);
    }

    fn air(&self) -> &Self::Air {
        &self.air
    }
}

// Returns (cmp_result, diff_idx, x_sign, y_sign)
pub(super) fn run_cmp<const NUM_LIMBS: usize, const LIMB_BITS: usize>(
    local_opcode: BranchLessThanOpcode,
    x: &[u32; NUM_LIMBS],
    y: &[u32; NUM_LIMBS],
) -> (bool, usize, bool, bool) {
    let signed =
        local_opcode == BranchLessThanOpcode::BLT || local_opcode == BranchLessThanOpcode::BGE;
    let ge_op =
        local_opcode == BranchLessThanOpcode::BGE || local_opcode == BranchLessThanOpcode::BGEU;
    let x_sign = (x[NUM_LIMBS - 1] >> (LIMB_BITS - 1) == 1) && signed;
    let y_sign = (y[NUM_LIMBS - 1] >> (LIMB_BITS - 1) == 1) && signed;
    for i in (0..NUM_LIMBS).rev() {
        if x[i] != y[i] {
            return ((x[i] < y[i]) ^ x_sign ^ y_sign ^ ge_op, i, x_sign, y_sign);
        }
    }
    (ge_op, NUM_LIMBS, x_sign, y_sign)
}
