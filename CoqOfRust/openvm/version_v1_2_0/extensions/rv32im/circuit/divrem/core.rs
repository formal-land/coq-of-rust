use std::{
    array,
    borrow::{Borrow, BorrowMut},
};

use num_bigint::BigUint;
use num_integer::Integer;
use openvm_circuit::arch::{
    AdapterAirContext, AdapterRuntimeContext, MinimalInstruction, Result, VmAdapterInterface,
    VmCoreAir, VmCoreChip,
};
use openvm_circuit_primitives::{
    bitwise_op_lookup::{BitwiseOperationLookupBus, SharedBitwiseOperationLookupChip},
    range_tuple::{RangeTupleCheckerBus, SharedRangeTupleCheckerChip},
    utils::{not, select},
};
use openvm_circuit_primitives_derive::AlignedBorrow;
use openvm_instructions::{instruction::Instruction, LocalOpcode};
use openvm_rv32im_transpiler::DivRemOpcode;
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
#[derive(AlignedBorrow)]
pub struct DivRemCoreCols<T, const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    // b = c * q + r for some 0 <= |r| < |c| and sign(r) = sign(b).
    pub b: [T; NUM_LIMBS],
    pub c: [T; NUM_LIMBS],
    pub q: [T; NUM_LIMBS],
    pub r: [T; NUM_LIMBS],

    // Flags to indicate special cases.
    pub zero_divisor: T,
    pub r_zero: T,

    // Sign of b and c respectively, while q_sign = b_sign ^ c_sign if q is non-zero
    // and is 0 otherwise. sign_xor = b_sign ^ c_sign always.
    pub b_sign: T,
    pub c_sign: T,
    pub q_sign: T,
    pub sign_xor: T,

    // Auxiliary columns to constrain that zero_divisor = 1 if and only if c = 0.
    pub c_sum_inv: T,
    // Auxiliary columns to constrain that r_zero = 1 if and only if r = 0 and zero_divisor = 0.
    pub r_sum_inv: T,

    // Auxiliary columns to constrain that 0 <= |r| < |c|. When sign_xor == 1 we have
    // r_prime = -r, and when sign_xor == 0 we have r_prime = r. Each r_inv[i] is the
    // field inverse of r_prime[i] - 2^LIMB_BITS, ensures each r_prime[i] is in range.
    pub r_prime: [T; NUM_LIMBS],
    pub r_inv: [T; NUM_LIMBS],
    pub lt_marker: [T; NUM_LIMBS],
    pub lt_diff: T,

    // Opcode flags
    pub opcode_div_flag: T,
    pub opcode_divu_flag: T,
    pub opcode_rem_flag: T,
    pub opcode_remu_flag: T,
}

#[derive(Copy, Clone, Debug)]
pub struct DivRemCoreAir<const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    pub bitwise_lookup_bus: BitwiseOperationLookupBus,
    pub range_tuple_bus: RangeTupleCheckerBus<2>,
    offset: usize,
}

impl<F: Field, const NUM_LIMBS: usize, const LIMB_BITS: usize> BaseAir<F>
    for DivRemCoreAir<NUM_LIMBS, LIMB_BITS>
{
    fn width(&self) -> usize {
        DivRemCoreCols::<F, NUM_LIMBS, LIMB_BITS>::width()
    }
}
impl<F: Field, const NUM_LIMBS: usize, const LIMB_BITS: usize> BaseAirWithPublicValues<F>
    for DivRemCoreAir<NUM_LIMBS, LIMB_BITS>
{
}

impl<AB, I, const NUM_LIMBS: usize, const LIMB_BITS: usize> VmCoreAir<AB, I>
    for DivRemCoreAir<NUM_LIMBS, LIMB_BITS>
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
        let cols: &DivRemCoreCols<_, NUM_LIMBS, LIMB_BITS> = local_core.borrow();
        let flags = [
            cols.opcode_div_flag,
            cols.opcode_divu_flag,
            cols.opcode_rem_flag,
            cols.opcode_remu_flag,
        ];

        let is_valid = flags.iter().fold(AB::Expr::ZERO, |acc, &flag| {
            builder.assert_bool(flag);
            acc + flag.into()
        });
        builder.assert_bool(is_valid.clone());

        let b = &cols.b;
        let c = &cols.c;
        let q = &cols.q;
        let r = &cols.r;

        // Constrain that b = (c * q + r) % 2^{NUM_LIMBS * LIMB_BITS} and range checkeach element in
        // q.
        let b_ext = cols.b_sign * AB::F::from_canonical_u32((1 << LIMB_BITS) - 1);
        let c_ext = cols.c_sign * AB::F::from_canonical_u32((1 << LIMB_BITS) - 1);
        let carry_divide = AB::F::from_canonical_u32(1 << LIMB_BITS).inverse();
        let mut carry: [AB::Expr; NUM_LIMBS] = array::from_fn(|_| AB::Expr::ZERO);

        for i in 0..NUM_LIMBS {
            let expected_limb = if i == 0 {
                AB::Expr::ZERO
            } else {
                carry[i - 1].clone()
            } + (0..=i).fold(r[i].into(), |ac, k| ac + (c[k] * q[i - k]));
            carry[i] = (expected_limb - b[i]) * carry_divide;
        }

        for (q, carry) in q.iter().zip(carry.iter()) {
            self.range_tuple_bus
                .send(vec![(*q).into(), carry.clone()])
                .eval(builder, is_valid.clone());
        }

        // Constrain that the upper limbs of b = c * q + r are all equal to b_ext and
        // range check each element in r.
        let q_ext = cols.q_sign * AB::F::from_canonical_u32((1 << LIMB_BITS) - 1);
        let mut carry_ext: [AB::Expr; NUM_LIMBS] = array::from_fn(|_| AB::Expr::ZERO);

        for j in 0..NUM_LIMBS {
            let expected_limb = if j == 0 {
                carry[NUM_LIMBS - 1].clone()
            } else {
                carry_ext[j - 1].clone()
            } + ((j + 1)..NUM_LIMBS)
                .fold(AB::Expr::ZERO, |acc, k| acc + (c[k] * q[NUM_LIMBS + j - k]))
                + (0..(j + 1)).fold(AB::Expr::ZERO, |acc, k| {
                    acc + (c[k] * q_ext.clone()) + (q[k] * c_ext.clone())
                })
                + (AB::Expr::ONE - cols.r_zero) * b_ext.clone();
            // Technically there are ways to constrain that c * q is in range without
            // using a range checker, but because we already have to range check each
            // limb of r it requires no additional columns to also range check each
            // carry_ext.
            //
            // Note that the sign of r is not equal to the sign of b only when r = 0.
            // Flag column r_zero tracks this special case.
            carry_ext[j] = (expected_limb - b_ext.clone()) * carry_divide;
        }

        for (r, carry) in r.iter().zip(carry_ext.iter()) {
            self.range_tuple_bus
                .send(vec![(*r).into(), carry.clone()])
                .eval(builder, is_valid.clone());
        }

        // Handle special cases. We can have either at most one of a zero divisor,
        // or a 0 remainder. Signed overflow falls under the latter.
        let special_case = cols.zero_divisor + cols.r_zero;
        builder.assert_bool(special_case.clone());

        // Constrain that zero_divisor = 1 if and only if c = 0.
        builder.assert_bool(cols.zero_divisor);
        let mut when_zero_divisor = builder.when(cols.zero_divisor);
        for i in 0..NUM_LIMBS {
            when_zero_divisor.assert_zero(c[i]);
            when_zero_divisor.assert_eq(q[i], AB::F::from_canonical_u32((1 << LIMB_BITS) - 1));
        }
        // c_sum is guaranteed to be non-zero if c is non-zero since we assume
        // each limb of c to be within [0, 2^LIMB_BITS) already.
        // To constrain that if c = 0 then zero_divisor = 1, we check that if zero_divisor = 0
        // and is_valid = 1 then c_sum is non-zero using c_sum_inv.
        let c_sum = c.iter().fold(AB::Expr::ZERO, |acc, c| acc + *c);
        let valid_and_not_zero_divisor = is_valid.clone() - cols.zero_divisor;
        builder.assert_bool(valid_and_not_zero_divisor.clone());
        builder
            .when(valid_and_not_zero_divisor)
            .assert_one(c_sum * cols.c_sum_inv);

        // Constrain that r_zero = 1 if and only if r = 0 and zero_divisor = 0.
        builder.assert_bool(cols.r_zero);
        r.iter()
            .for_each(|r_i| builder.when(cols.r_zero).assert_zero(*r_i));
        // To constrain that if r = 0 and zero_divisor = 0 then r_zero = 1, we check that
        // if special_case = 0 and is_valid = 1 then r_sum is non-zero (using r_sum_inv).
        let r_sum = r.iter().fold(AB::Expr::ZERO, |acc, r| acc + *r);
        let valid_and_not_special_case = is_valid.clone() - special_case.clone();
        builder.assert_bool(valid_and_not_special_case.clone());
        builder
            .when(valid_and_not_special_case)
            .assert_one(r_sum * cols.r_sum_inv);

        // Constrain the correctness of b_sign and c_sign. Note that we do not need to
        // check that the sign of r is b_sign since we cannot have r_prime < c (or c < r_prime
        // if c is negative) if this is not the case.
        let signed = cols.opcode_div_flag + cols.opcode_rem_flag;

        builder.assert_bool(cols.b_sign);
        builder.assert_bool(cols.c_sign);
        builder
            .when(not::<AB::Expr>(signed.clone()))
            .assert_zero(cols.b_sign);
        builder
            .when(not::<AB::Expr>(signed.clone()))
            .assert_zero(cols.c_sign);
        builder.assert_eq(
            cols.b_sign + cols.c_sign - AB::Expr::from_canonical_u32(2) * cols.b_sign * cols.c_sign,
            cols.sign_xor,
        );

        // To constrain the correctness of q_sign we make sure if q is non-zero then
        // q_sign = b_sign ^ c_sign, and if q is zero then q_sign = 0.
        // Note:
        // - q_sum is guaranteed to be non-zero if q is non-zero since we've range checked each
        // limb of q to be within [0, 2^LIMB_BITS) already.
        // - If q is zero and q_ext satisfies the constraint
        // sign_extend(b) = sign_extend(c) * sign_extend(q) + sign_extend(r), then q_sign must be 0.
        // Thus, we do not need additional constraints in case q is zero.
        let nonzero_q = q.iter().fold(AB::Expr::ZERO, |acc, q| acc + *q);
        builder.assert_bool(cols.q_sign);
        builder
            .when(nonzero_q)
            .when(not(cols.zero_divisor))
            .assert_eq(cols.q_sign, cols.sign_xor);
        builder
            .when_ne(cols.q_sign, cols.sign_xor)
            .when(not(cols.zero_divisor))
            .assert_zero(cols.q_sign);

        // Check that the signs of b and c are correct.
        let sign_mask = AB::F::from_canonical_u32(1 << (LIMB_BITS - 1));
        self.bitwise_lookup_bus
            .send_range(
                AB::Expr::from_canonical_u32(2) * (b[NUM_LIMBS - 1] - cols.b_sign * sign_mask),
                AB::Expr::from_canonical_u32(2) * (c[NUM_LIMBS - 1] - cols.c_sign * sign_mask),
            )
            .eval(builder, signed.clone());

        // Constrain that 0 <= |r| < |c| by checking that r_prime < c (unsigned LT). By
        // definition, the sign of r must be b_sign. If c is negative then we want
        // to constrain c < r_prime. If c is positive, then we want to constrain r_prime < c.
        //
        // Because we already constrain that r and q are correct for special cases,
        // we skip the range check when special_case = 1.
        let r_p = &cols.r_prime;
        let mut carry_lt: [AB::Expr; NUM_LIMBS] = array::from_fn(|_| AB::Expr::ZERO);

        for i in 0..NUM_LIMBS {
            // When the signs of r (i.e. b) and c are the same, r_prime = r.
            builder.when(not(cols.sign_xor)).assert_eq(r[i], r_p[i]);

            // When the signs of r and c are different, r_prime = -r. To constrain this, we
            // first ensure each r[i] + r_prime[i] + carry[i - 1] is in {0, 2^LIMB_BITS}, and
            // that when the sum is 0 then r_prime[i] = 0 as well. Passing both constraints
            // implies that 0 <= r_prime[i] <= 2^LIMB_BITS, and in order to ensure r_prime[i] !=
            // 2^LIMB_BITS we check that r_prime[i] - 2^LIMB_BITS has an inverse in F.
            let last_carry = if i > 0 {
                carry_lt[i - 1].clone()
            } else {
                AB::Expr::ZERO
            };
            carry_lt[i] = (last_carry.clone() + r[i] + r_p[i]) * carry_divide;
            builder.when(cols.sign_xor).assert_zero(
                (carry_lt[i].clone() - last_carry) * (carry_lt[i].clone() - AB::Expr::ONE),
            );
            builder
                .when(cols.sign_xor)
                .assert_one((r_p[i] - AB::F::from_canonical_u32(1 << LIMB_BITS)) * cols.r_inv[i]);
            builder
                .when(cols.sign_xor)
                .when(not::<AB::Expr>(carry_lt[i].clone()))
                .assert_zero(r_p[i]);
        }

        let marker = &cols.lt_marker;
        let mut prefix_sum = special_case.clone();

        for i in (0..NUM_LIMBS).rev() {
            let diff = r_p[i] * (AB::Expr::from_canonical_u8(2) * cols.c_sign - AB::Expr::ONE)
                + c[i] * (AB::Expr::ONE - AB::Expr::from_canonical_u8(2) * cols.c_sign);
            prefix_sum += marker[i].into();
            builder.assert_bool(marker[i]);
            builder.assert_zero(not::<AB::Expr>(prefix_sum.clone()) * diff.clone());
            builder.when(marker[i]).assert_eq(cols.lt_diff, diff);
        }
        // - If r_prime != c, then prefix_sum = 1 so marker[i] must be 1 iff i is the first index
        //   where diff != 0. Constrains that diff == lt_diff where lt_diff is non-zero.
        // - If r_prime == c, then prefix_sum = 0. Here, prefix_sum cannot be 1 because all diff are
        //   zero, making diff == lt_diff fails.

        builder.when(is_valid.clone()).assert_one(prefix_sum);
        // Range check to ensure lt_diff is non-zero.
        self.bitwise_lookup_bus
            .send_range(cols.lt_diff - AB::Expr::ONE, AB::F::ZERO)
            .eval(builder, is_valid.clone() - special_case);

        // Generate expected opcode and output a to pass to the adapter.
        let expected_opcode = flags.iter().zip(DivRemOpcode::iter()).fold(
            AB::Expr::ZERO,
            |acc, (flag, local_opcode)| {
                acc + (*flag).into() * AB::Expr::from_canonical_u8(local_opcode as u8)
            },
        ) + AB::Expr::from_canonical_usize(self.offset);

        let is_div = cols.opcode_div_flag + cols.opcode_divu_flag;
        let a = array::from_fn(|i| select(is_div.clone(), q[i], r[i]));

        AdapterAirContext {
            to_pc: None,
            reads: [cols.b.map(Into::into), cols.c.map(Into::into)].into(),
            writes: [a.map(Into::into)].into(),
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

pub struct DivRemCoreChip<const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    pub air: DivRemCoreAir<NUM_LIMBS, LIMB_BITS>,
    pub bitwise_lookup_chip: SharedBitwiseOperationLookupChip<LIMB_BITS>,
    pub range_tuple_chip: SharedRangeTupleCheckerChip<2>,
}

impl<const NUM_LIMBS: usize, const LIMB_BITS: usize> DivRemCoreChip<NUM_LIMBS, LIMB_BITS> {
    pub fn new(
        bitwise_lookup_chip: SharedBitwiseOperationLookupChip<LIMB_BITS>,
        range_tuple_chip: SharedRangeTupleCheckerChip<2>,
        offset: usize,
    ) -> Self {
        // The RangeTupleChecker is used to range check (a[i], carry[i]) pairs where 0 <= i
        // < 2 * NUM_LIMBS. a[i] must have LIMB_BITS bits and carry[i] is the sum of i + 1
        // bytes (with LIMB_BITS bits). BitwiseOperationLookup is used to sign check bytes.
        debug_assert!(
            range_tuple_chip.sizes()[0] == 1 << LIMB_BITS,
            "First element of RangeTupleChecker must have size {}",
            1 << LIMB_BITS
        );
        debug_assert!(
            range_tuple_chip.sizes()[1] >= (1 << LIMB_BITS) * 2 * NUM_LIMBS as u32,
            "Second element of RangeTupleChecker must have size of at least {}",
            (1 << LIMB_BITS) * 2 * NUM_LIMBS as u32
        );

        Self {
            air: DivRemCoreAir {
                bitwise_lookup_bus: bitwise_lookup_chip.bus(),
                range_tuple_bus: *range_tuple_chip.bus(),
                offset,
            },
            bitwise_lookup_chip,
            range_tuple_chip,
        }
    }
}

#[repr(C)]
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "T: Serialize + DeserializeOwned")]
pub struct DivRemCoreRecord<T, const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    #[serde(with = "BigArray")]
    pub b: [T; NUM_LIMBS],
    #[serde(with = "BigArray")]
    pub c: [T; NUM_LIMBS],
    #[serde(with = "BigArray")]
    pub q: [T; NUM_LIMBS],
    #[serde(with = "BigArray")]
    pub r: [T; NUM_LIMBS],
    pub zero_divisor: T,
    pub r_zero: T,
    pub b_sign: T,
    pub c_sign: T,
    pub q_sign: T,
    pub sign_xor: T,
    pub c_sum_inv: T,
    pub r_sum_inv: T,
    #[serde(with = "BigArray")]
    pub r_prime: [T; NUM_LIMBS],
    #[serde(with = "BigArray")]
    pub r_inv: [T; NUM_LIMBS],
    pub lt_diff_val: T,
    pub lt_diff_idx: usize,
    pub opcode: DivRemOpcode,
}

#[derive(Debug, Eq, PartialEq)]
#[repr(u8)]
pub(super) enum DivRemCoreSpecialCase {
    None,
    ZeroDivisor,
    SignedOverflow,
}

impl<F: PrimeField32, I: VmAdapterInterface<F>, const NUM_LIMBS: usize, const LIMB_BITS: usize>
    VmCoreChip<F, I> for DivRemCoreChip<NUM_LIMBS, LIMB_BITS>
where
    I::Reads: Into<[[F; NUM_LIMBS]; 2]>,
    I::Writes: From<[[F; NUM_LIMBS]; 1]>,
{
    type Record = DivRemCoreRecord<F, NUM_LIMBS, LIMB_BITS>;
    type Air = DivRemCoreAir<NUM_LIMBS, LIMB_BITS>;

    #[allow(clippy::type_complexity)]
    fn execute_instruction(
        &self,
        instruction: &Instruction<F>,
        _from_pc: u32,
        reads: I::Reads,
    ) -> Result<(AdapterRuntimeContext<F, I>, Self::Record)> {
        let Instruction { opcode, .. } = instruction;
        let divrem_opcode = DivRemOpcode::from_usize(opcode.local_opcode_idx(self.air.offset));

        let is_div = divrem_opcode == DivRemOpcode::DIV || divrem_opcode == DivRemOpcode::DIVU;
        let is_signed = divrem_opcode == DivRemOpcode::DIV || divrem_opcode == DivRemOpcode::REM;

        let data: [[F; NUM_LIMBS]; 2] = reads.into();
        let b = data[0].map(|x| x.as_canonical_u32());
        let c = data[1].map(|y| y.as_canonical_u32());
        let (q, r, b_sign, c_sign, q_sign, case) =
            run_divrem::<NUM_LIMBS, LIMB_BITS>(is_signed, &b, &c);

        let carries = run_mul_carries::<NUM_LIMBS, LIMB_BITS>(is_signed, &c, &q, &r, q_sign);
        for i in 0..NUM_LIMBS {
            self.range_tuple_chip.add_count(&[q[i], carries[i]]);
            self.range_tuple_chip
                .add_count(&[r[i], carries[i + NUM_LIMBS]]);
        }

        let sign_xor = b_sign ^ c_sign;
        let r_prime = if sign_xor {
            negate::<NUM_LIMBS, LIMB_BITS>(&r)
        } else {
            r
        };
        let r_zero = r.iter().all(|&v| v == 0) && case != DivRemCoreSpecialCase::ZeroDivisor;

        if is_signed {
            let b_sign_mask = if b_sign { 1 << (LIMB_BITS - 1) } else { 0 };
            let c_sign_mask = if c_sign { 1 << (LIMB_BITS - 1) } else { 0 };
            self.bitwise_lookup_chip.request_range(
                (b[NUM_LIMBS - 1] - b_sign_mask) << 1,
                (c[NUM_LIMBS - 1] - c_sign_mask) << 1,
            );
        }

        let c_sum_f = data[1].iter().fold(F::ZERO, |acc, c| acc + *c);
        let c_sum_inv_f = c_sum_f.try_inverse().unwrap_or(F::ZERO);

        let r_sum_f = r
            .iter()
            .fold(F::ZERO, |acc, r| acc + F::from_canonical_u32(*r));
        let r_sum_inv_f = r_sum_f.try_inverse().unwrap_or(F::ZERO);

        let (lt_diff_idx, lt_diff_val) = if case == DivRemCoreSpecialCase::None && !r_zero {
            let idx = run_sltu_diff_idx(&c, &r_prime, c_sign);
            let val = if c_sign {
                r_prime[idx] - c[idx]
            } else {
                c[idx] - r_prime[idx]
            };
            self.bitwise_lookup_chip.request_range(val - 1, 0);
            (idx, val)
        } else {
            (NUM_LIMBS, 0)
        };

        let r_prime_f = r_prime.map(F::from_canonical_u32);
        let output = AdapterRuntimeContext::without_pc([
            (if is_div { &q } else { &r }).map(F::from_canonical_u32)
        ]);
        let record = DivRemCoreRecord {
            opcode: divrem_opcode,
            b: data[0],
            c: data[1],
            q: q.map(F::from_canonical_u32),
            r: r.map(F::from_canonical_u32),
            zero_divisor: F::from_bool(case == DivRemCoreSpecialCase::ZeroDivisor),
            r_zero: F::from_bool(r_zero),
            b_sign: F::from_bool(b_sign),
            c_sign: F::from_bool(c_sign),
            q_sign: F::from_bool(q_sign),
            sign_xor: F::from_bool(sign_xor),
            c_sum_inv: c_sum_inv_f,
            r_sum_inv: r_sum_inv_f,
            r_prime: r_prime_f,
            r_inv: r_prime_f.map(|r| (r - F::from_canonical_u32(256)).inverse()),
            lt_diff_val: F::from_canonical_u32(lt_diff_val),
            lt_diff_idx,
        };

        Ok((output, record))
    }

    fn get_opcode_name(&self, opcode: usize) -> String {
        format!("{:?}", DivRemOpcode::from_usize(opcode - self.air.offset))
    }

    fn generate_trace_row(&self, row_slice: &mut [F], record: Self::Record) {
        let row_slice: &mut DivRemCoreCols<_, NUM_LIMBS, LIMB_BITS> = row_slice.borrow_mut();
        row_slice.b = record.b;
        row_slice.c = record.c;
        row_slice.q = record.q;
        row_slice.r = record.r;
        row_slice.zero_divisor = record.zero_divisor;
        row_slice.r_zero = record.r_zero;
        row_slice.b_sign = record.b_sign;
        row_slice.c_sign = record.c_sign;
        row_slice.q_sign = record.q_sign;
        row_slice.sign_xor = record.sign_xor;
        row_slice.c_sum_inv = record.c_sum_inv;
        row_slice.r_sum_inv = record.r_sum_inv;
        row_slice.r_prime = record.r_prime;
        row_slice.r_inv = record.r_inv;
        row_slice.lt_marker = array::from_fn(|i| F::from_bool(i == record.lt_diff_idx));
        row_slice.lt_diff = record.lt_diff_val;
        row_slice.opcode_div_flag = F::from_bool(record.opcode == DivRemOpcode::DIV);
        row_slice.opcode_divu_flag = F::from_bool(record.opcode == DivRemOpcode::DIVU);
        row_slice.opcode_rem_flag = F::from_bool(record.opcode == DivRemOpcode::REM);
        row_slice.opcode_remu_flag = F::from_bool(record.opcode == DivRemOpcode::REMU);
    }

    fn air(&self) -> &Self::Air {
        &self.air
    }
}

// Returns (quotient, remainder, x_sign, y_sign, q_sign, case) where case = 0 for normal, 1
// for zero divisor, and 2 for signed overflow
pub(super) fn run_divrem<const NUM_LIMBS: usize, const LIMB_BITS: usize>(
    signed: bool,
    x: &[u32; NUM_LIMBS],
    y: &[u32; NUM_LIMBS],
) -> (
    [u32; NUM_LIMBS],
    [u32; NUM_LIMBS],
    bool,
    bool,
    bool,
    DivRemCoreSpecialCase,
) {
    let x_sign = signed && (x[NUM_LIMBS - 1] >> (LIMB_BITS - 1) == 1);
    let y_sign = signed && (y[NUM_LIMBS - 1] >> (LIMB_BITS - 1) == 1);
    let max_limb = (1 << LIMB_BITS) - 1;

    let zero_divisor = y.iter().all(|val| *val == 0);
    let overflow = x[NUM_LIMBS - 1] == 1 << (LIMB_BITS - 1)
        && x[..(NUM_LIMBS - 1)].iter().all(|val| *val == 0)
        && y.iter().all(|val| *val == max_limb)
        && x_sign
        && y_sign;

    if zero_divisor {
        return (
            [max_limb; NUM_LIMBS],
            *x,
            x_sign,
            y_sign,
            signed,
            DivRemCoreSpecialCase::ZeroDivisor,
        );
    } else if overflow {
        return (
            *x,
            [0; NUM_LIMBS],
            x_sign,
            y_sign,
            false,
            DivRemCoreSpecialCase::SignedOverflow,
        );
    }

    let x_abs = if x_sign {
        negate::<NUM_LIMBS, LIMB_BITS>(x)
    } else {
        *x
    };
    let y_abs = if y_sign {
        negate::<NUM_LIMBS, LIMB_BITS>(y)
    } else {
        *y
    };

    let x_big = limbs_to_biguint::<NUM_LIMBS, LIMB_BITS>(&x_abs);
    let y_big = limbs_to_biguint::<NUM_LIMBS, LIMB_BITS>(&y_abs);
    let q_big = x_big.clone() / y_big.clone();
    let r_big = x_big.clone() % y_big.clone();

    let q = if x_sign ^ y_sign {
        negate::<NUM_LIMBS, LIMB_BITS>(&biguint_to_limbs::<NUM_LIMBS, LIMB_BITS>(&q_big))
    } else {
        biguint_to_limbs::<NUM_LIMBS, LIMB_BITS>(&q_big)
    };
    let q_sign = signed && (q[NUM_LIMBS - 1] >> (LIMB_BITS - 1) == 1);

    // In C |q * y| <= |x|, which means if x is negative then r <= 0 and vice versa.
    let r = if x_sign {
        negate::<NUM_LIMBS, LIMB_BITS>(&biguint_to_limbs::<NUM_LIMBS, LIMB_BITS>(&r_big))
    } else {
        biguint_to_limbs::<NUM_LIMBS, LIMB_BITS>(&r_big)
    };

    (q, r, x_sign, y_sign, q_sign, DivRemCoreSpecialCase::None)
}

pub(super) fn run_sltu_diff_idx<const NUM_LIMBS: usize>(
    x: &[u32; NUM_LIMBS],
    y: &[u32; NUM_LIMBS],
    cmp: bool,
) -> usize {
    for i in (0..NUM_LIMBS).rev() {
        if x[i] != y[i] {
            assert!((x[i] < y[i]) == cmp);
            return i;
        }
    }
    assert!(!cmp);
    NUM_LIMBS
}

// returns carries of d * q + r
pub(super) fn run_mul_carries<const NUM_LIMBS: usize, const LIMB_BITS: usize>(
    signed: bool,
    d: &[u32; NUM_LIMBS],
    q: &[u32; NUM_LIMBS],
    r: &[u32; NUM_LIMBS],
    q_sign: bool,
) -> Vec<u32> {
    let mut carry = vec![0u32; 2 * NUM_LIMBS];
    for i in 0..NUM_LIMBS {
        let mut val = r[i] + if i > 0 { carry[i - 1] } else { 0 };
        for j in 0..=i {
            val += d[j] * q[i - j];
        }
        carry[i] = val >> LIMB_BITS;
    }

    let q_ext = if q_sign && signed {
        (1 << LIMB_BITS) - 1
    } else {
        0
    };
    let d_ext =
        (d[NUM_LIMBS - 1] >> (LIMB_BITS - 1)) * if signed { (1 << LIMB_BITS) - 1 } else { 0 };
    let r_ext =
        (r[NUM_LIMBS - 1] >> (LIMB_BITS - 1)) * if signed { (1 << LIMB_BITS) - 1 } else { 0 };
    let mut d_prefix = 0;
    let mut q_prefix = 0;

    for i in 0..NUM_LIMBS {
        d_prefix += d[i];
        q_prefix += q[i];
        let mut val = carry[NUM_LIMBS + i - 1] + d_prefix * q_ext + q_prefix * d_ext + r_ext;
        for j in (i + 1)..NUM_LIMBS {
            val += d[j] * q[NUM_LIMBS + i - j];
        }
        carry[NUM_LIMBS + i] = val >> LIMB_BITS;
    }
    carry
}

fn limbs_to_biguint<const NUM_LIMBS: usize, const LIMB_BITS: usize>(
    x: &[u32; NUM_LIMBS],
) -> BigUint {
    let base = BigUint::new(vec![1 << LIMB_BITS]);
    let mut res = BigUint::new(vec![0]);
    for val in x.iter().rev() {
        res *= base.clone();
        res += BigUint::new(vec![*val]);
    }
    res
}

fn biguint_to_limbs<const NUM_LIMBS: usize, const LIMB_BITS: usize>(
    x: &BigUint,
) -> [u32; NUM_LIMBS] {
    let mut res = [0; NUM_LIMBS];
    let mut x = x.clone();
    let base = BigUint::from(1u32 << LIMB_BITS);
    for limb in res.iter_mut() {
        let (quot, rem) = x.div_rem(&base);
        *limb = rem.iter_u32_digits().next().unwrap_or(0);
        x = quot;
    }
    debug_assert_eq!(x, BigUint::from(0u32));
    res
}

fn negate<const NUM_LIMBS: usize, const LIMB_BITS: usize>(
    x: &[u32; NUM_LIMBS],
) -> [u32; NUM_LIMBS] {
    let mut carry = 1;
    array::from_fn(|i| {
        let val = (1 << LIMB_BITS) + carry - 1 - x[i];
        carry = val >> LIMB_BITS;
        val % (1 << LIMB_BITS)
    })
}
