use std::{
    array,
    borrow::{Borrow, BorrowMut},
};

use openvm_circuit::arch::{
    AdapterAirContext, AdapterRuntimeContext, MinimalInstruction, Result, VmAdapterInterface,
    VmCoreAir, VmCoreChip,
};
use openvm_circuit_primitives::range_tuple::{RangeTupleCheckerBus, SharedRangeTupleCheckerChip};
use openvm_circuit_primitives_derive::AlignedBorrow;
use openvm_instructions::{instruction::Instruction, LocalOpcode};
use openvm_rv32im_transpiler::MulOpcode;
use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::BaseAir,
    p3_field::{Field, FieldAlgebra, PrimeField32},
    rap::BaseAirWithPublicValues,
};
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use serde_big_array::BigArray;

#[repr(C)]
#[derive(AlignedBorrow)]
pub struct MultiplicationCoreCols<T, const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    pub a: [T; NUM_LIMBS],
    pub b: [T; NUM_LIMBS],
    pub c: [T; NUM_LIMBS],
    pub is_valid: T,
}

#[derive(Copy, Clone, Debug)]
pub struct MultiplicationCoreAir<const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    pub bus: RangeTupleCheckerBus<2>,
    pub offset: usize,
}

impl<F: Field, const NUM_LIMBS: usize, const LIMB_BITS: usize> BaseAir<F>
    for MultiplicationCoreAir<NUM_LIMBS, LIMB_BITS>
{
    fn width(&self) -> usize {
        MultiplicationCoreCols::<F, NUM_LIMBS, LIMB_BITS>::width()
    }
}
impl<F: Field, const NUM_LIMBS: usize, const LIMB_BITS: usize> BaseAirWithPublicValues<F>
    for MultiplicationCoreAir<NUM_LIMBS, LIMB_BITS>
{
}

impl<AB, I, const NUM_LIMBS: usize, const LIMB_BITS: usize> VmCoreAir<AB, I>
    for MultiplicationCoreAir<NUM_LIMBS, LIMB_BITS>
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
        let cols: &MultiplicationCoreCols<_, NUM_LIMBS, LIMB_BITS> = local_core.borrow();
        builder.assert_bool(cols.is_valid);

        let a = &cols.a;
        let b = &cols.b;
        let c = &cols.c;

        // Define carry[i] = (sum_{k=0}^{i} b[k] * c[i - k] + carry[i - 1] - a[i]) / 2^LIMB_BITS.
        // If 0 <= a[i], carry[i] < 2^LIMB_BITS, it can be proven that a[i] = sum_{k=0}^{i} (b[k] *
        // c[i - k]) % 2^LIMB_BITS as necessary.
        let mut carry: [AB::Expr; NUM_LIMBS] = array::from_fn(|_| AB::Expr::ZERO);
        let carry_divide = AB::F::from_canonical_u32(1 << LIMB_BITS).inverse();

        for i in 0..NUM_LIMBS {
            let expected_limb = if i == 0 {
                AB::Expr::ZERO
            } else {
                carry[i - 1].clone()
            } + (0..=i).fold(AB::Expr::ZERO, |acc, k| acc + (b[k] * c[i - k]));
            carry[i] = AB::Expr::from(carry_divide) * (expected_limb - a[i]);
        }

        for (a, carry) in a.iter().zip(carry.iter()) {
            self.bus
                .send(vec![(*a).into(), carry.clone()])
                .eval(builder, cols.is_valid);
        }

        let expected_opcode = VmCoreAir::<AB, I>::opcode_to_global_expr(self, MulOpcode::MUL);

        AdapterAirContext {
            to_pc: None,
            reads: [cols.b.map(Into::into), cols.c.map(Into::into)].into(),
            writes: [cols.a.map(Into::into)].into(),
            instruction: MinimalInstruction {
                is_valid: cols.is_valid.into(),
                opcode: expected_opcode,
            }
            .into(),
        }
    }

    fn start_offset(&self) -> usize {
        self.offset
    }
}

#[derive(Debug)]
pub struct MultiplicationCoreChip<const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    pub air: MultiplicationCoreAir<NUM_LIMBS, LIMB_BITS>,
    pub range_tuple_chip: SharedRangeTupleCheckerChip<2>,
}

impl<const NUM_LIMBS: usize, const LIMB_BITS: usize> MultiplicationCoreChip<NUM_LIMBS, LIMB_BITS> {
    pub fn new(range_tuple_chip: SharedRangeTupleCheckerChip<2>, offset: usize) -> Self {
        // The RangeTupleChecker is used to range check (a[i], carry[i]) pairs where 0 <= i
        // < NUM_LIMBS. a[i] must have LIMB_BITS bits and carry[i] is the sum of i + 1 bytes
        // (with LIMB_BITS bits).
        debug_assert!(
            range_tuple_chip.sizes()[0] == 1 << LIMB_BITS,
            "First element of RangeTupleChecker must have size {}",
            1 << LIMB_BITS
        );
        debug_assert!(
            range_tuple_chip.sizes()[1] >= (1 << LIMB_BITS) * NUM_LIMBS as u32,
            "Second element of RangeTupleChecker must have size of at least {}",
            (1 << LIMB_BITS) * NUM_LIMBS as u32
        );

        Self {
            air: MultiplicationCoreAir {
                bus: *range_tuple_chip.bus(),
                offset,
            },
            range_tuple_chip,
        }
    }
}

#[repr(C)]
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "T: Serialize + DeserializeOwned")]
pub struct MultiplicationCoreRecord<T, const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    #[serde(with = "BigArray")]
    pub a: [T; NUM_LIMBS],
    #[serde(with = "BigArray")]
    pub b: [T; NUM_LIMBS],
    #[serde(with = "BigArray")]
    pub c: [T; NUM_LIMBS],
}

impl<F: PrimeField32, I: VmAdapterInterface<F>, const NUM_LIMBS: usize, const LIMB_BITS: usize>
    VmCoreChip<F, I> for MultiplicationCoreChip<NUM_LIMBS, LIMB_BITS>
where
    I::Reads: Into<[[F; NUM_LIMBS]; 2]>,
    I::Writes: From<[[F; NUM_LIMBS]; 1]>,
{
    type Record = MultiplicationCoreRecord<F, NUM_LIMBS, LIMB_BITS>;
    type Air = MultiplicationCoreAir<NUM_LIMBS, LIMB_BITS>;

    #[allow(clippy::type_complexity)]
    fn execute_instruction(
        &self,
        instruction: &Instruction<F>,
        _from_pc: u32,
        reads: I::Reads,
    ) -> Result<(AdapterRuntimeContext<F, I>, Self::Record)> {
        let Instruction { opcode, .. } = instruction;
        assert_eq!(
            MulOpcode::from_usize(opcode.local_opcode_idx(self.air.offset)),
            MulOpcode::MUL
        );

        let data: [[F; NUM_LIMBS]; 2] = reads.into();
        let b = data[0].map(|x| x.as_canonical_u32());
        let c = data[1].map(|y| y.as_canonical_u32());
        let (a, carry) = run_mul::<NUM_LIMBS, LIMB_BITS>(&b, &c);

        for (a, carry) in a.iter().zip(carry.iter()) {
            self.range_tuple_chip.add_count(&[*a, *carry]);
        }

        let output = AdapterRuntimeContext::without_pc([a.map(F::from_canonical_u32)]);
        let record = MultiplicationCoreRecord {
            a: a.map(F::from_canonical_u32),
            b: data[0],
            c: data[1],
        };

        Ok((output, record))
    }

    fn get_opcode_name(&self, opcode: usize) -> String {
        format!("{:?}", MulOpcode::from_usize(opcode - self.air.offset))
    }

    fn generate_trace_row(&self, row_slice: &mut [F], record: Self::Record) {
        let row_slice: &mut MultiplicationCoreCols<_, NUM_LIMBS, LIMB_BITS> =
            row_slice.borrow_mut();
        row_slice.a = record.a;
        row_slice.b = record.b;
        row_slice.c = record.c;
        row_slice.is_valid = F::ONE;
    }

    fn air(&self) -> &Self::Air {
        &self.air
    }
}

// returns mul, carry
pub(super) fn run_mul<const NUM_LIMBS: usize, const LIMB_BITS: usize>(
    x: &[u32; NUM_LIMBS],
    y: &[u32; NUM_LIMBS],
) -> ([u32; NUM_LIMBS], [u32; NUM_LIMBS]) {
    let mut result = [0; NUM_LIMBS];
    let mut carry = [0; NUM_LIMBS];
    for i in 0..NUM_LIMBS {
        if i > 0 {
            result[i] = carry[i - 1];
        }
        for j in 0..=i {
            result[i] += x[j] * y[i - j];
        }
        carry[i] = result[i] >> LIMB_BITS;
        result[i] %= 1 << LIMB_BITS;
    }
    (result, carry)
}
