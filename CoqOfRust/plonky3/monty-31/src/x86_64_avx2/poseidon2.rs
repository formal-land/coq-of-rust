//! Vectorized AVX2 implementation of Poseidon2 for MontyField31

use alloc::vec::Vec;
use core::arch::x86_64::{self, __m256i};
use core::marker::PhantomData;
use core::mem::transmute;

use p3_field::PrimeCharacteristicRing;
use p3_poseidon2::{
    ExternalLayer, ExternalLayerConstants, ExternalLayerConstructor, InternalLayer,
    InternalLayerConstructor, MDSMat4, external_initial_permute_state,
    external_terminal_permute_state,
};

use crate::{
    FieldParameters, InternalLayerBaseParameters, MontyField31, MontyParameters,
    PackedMontyField31AVX2, PackedMontyParameters, RelativelyPrimePower, add,
    apply_func_to_even_odd, halve_avx2, packed_exp_3, packed_exp_5, packed_exp_7, signed_add_avx2,
    sub,
};

// In the internal layers, it is valuable to treat the first entry of the state differently
// as it is the only entry to which we apply s-box.
// It seems to help the compiler if we introduce a different data structure for these layers.
// Note that we use this structure instead of a tuple so we can force the memory layout to align for transmutes.
#[derive(Clone, Copy)]
#[repr(C)] // This is needed to make `transmute`s safe.
pub struct InternalLayer16<PMP: PackedMontyParameters> {
    s0: PackedMontyField31AVX2<PMP>,
    s_hi: [__m256i; 15],
}

impl<PMP: PackedMontyParameters> InternalLayer16<PMP> {
    #[inline]
    #[must_use]
    /// Convert from `InternalLayer16<PMP>` to `[PackedMontyField31AVX2<PMP>; 16]`
    ///
    /// SAFETY: The caller must ensure that each element of `s_hi` represents a valid `MontyField31<PMP>`.
    /// In particular, each element of each vector must be in `[0, P)` (canonical form).
    unsafe fn to_packed_field_array(self) -> [PackedMontyField31AVX2<PMP>; 16] {
        unsafe {
            // Safety: It is up to the user to ensure that elements of `s_hi` represent valid
            // `MontyField31<PMP>` values. We must only reason about memory representations.
            // As described in packing.rs, PackedMontyField31AVX2<PMP> can be transmuted to and from `__m256i`.

            // `InternalLayer16` is `repr(C)` so its memory layout looks like:
            // `[PackedMontyField31AVX2<PMP>, __m256i, ..., __m256i]`
            // Thus as `__m256i` can be can be transmuted to `PackedMontyField31AVX2<FP>`,
            // `InternalLayer16` can be transmuted to `[PackedMontyField31AVX2<FP>; 16]`.
            transmute(self)
        }
    }

    #[inline]
    #[must_use]
    /// Convert from `[PackedMontyField31AVX2<PMP>; 16]` to `InternalLayer16<PMP>`
    fn from_packed_field_array(vector: [PackedMontyField31AVX2<PMP>; 16]) -> Self {
        unsafe {
            // Safety: As described in packing.rs, PackedMontyField31AVX2<PMP> can be transmuted to and from `__m256i`.

            // `InternalLayer16` is `repr(C)` so its memory layout looks like:
            // `[PackedMontyField31AVX2<PMP>, __m256i, ..., __m256i]`
            // Thus as `PackedMontyField31AVX2<FP>` can be can be transmuted to `__m256i`,
            // `[PackedMontyField31AVX2<FP>; 16]` can be transmuted to `InternalLayer16`.
            transmute(vector)
        }
    }
}

#[derive(Clone, Copy)]
#[repr(C)] // This is needed to make `transmute`s safe.
pub struct InternalLayer24<PMP: PackedMontyParameters> {
    s0: PackedMontyField31AVX2<PMP>,
    s_hi: [__m256i; 23],
}

impl<PMP: PackedMontyParameters> InternalLayer24<PMP> {
    #[inline]
    #[must_use]
    /// Convert from `InternalLayer24<PMP>` to `[PackedMontyField31AVX2<PMP>; 24]`
    ///
    /// SAFETY: The caller must ensure that each element of `s_hi` represents a valid `MontyField31<PMP>`.
    /// In particular, each element of each vector must be in `[0, P)` (canonical form).
    unsafe fn to_packed_field_array(self) -> [PackedMontyField31AVX2<PMP>; 24] {
        unsafe {
            // Safety: As described in packing.rs, PackedMontyField31AVX2<PMP> can be transmuted to and from `__m256i`.

            // `InternalLayer24` is `repr(C)` so its memory layout looks like:
            // `[PackedMontyField31AVX2<PMP>, __m256i, ..., __m256i]`
            // Thus as `__m256i` can be can be transmuted to `PackedMontyField31AVX2<FP>`,
            // `InternalLayer24` can be transmuted to `[PackedMontyField31AVX2<FP>; 24]`.
            transmute(self)
        }
    }

    #[inline]
    #[must_use]
    /// Convert from `[PackedMontyField31AVX2<PMP>; 24]` to `InternalLayer24<PMP>`
    fn from_packed_field_array(vector: [PackedMontyField31AVX2<PMP>; 24]) -> Self {
        unsafe {
            // Safety: As described in packing.rs, PackedMontyField31AVX2<PMP> can be transmuted to and from `__m256i`.

            // `InternalLayer24` is `repr(C)` so its memory layout looks like:
            // `[PackedMontyField31AVX2<PMP>, __m256i, ..., __m256i]`
            // Thus as `PackedMontyField31AVX2<FP>` can be can be transmuted to `__m256i`,
            // `[PackedMontyField31AVX2<FP>; 24]` can be transmuted to `InternalLayer24`.
            transmute(vector)
        }
    }
}

/// The internal layers of the Poseidon2 permutation for Monty31 fields.
///
/// The packed constants are stored in negative form as this allows some optimizations.
/// This means given a constant `x`, we treat it as an `i32` and
/// pack 8 copies of `x - P` into the corresponding `__m256i` packed constant.
#[derive(Debug, Clone)]
pub struct Poseidon2InternalLayerMonty31<
    PMP: PackedMontyParameters,
    const WIDTH: usize,
    ILP: InternalLayerParametersAVX2<PMP, WIDTH>,
> {
    pub(crate) internal_constants: Vec<MontyField31<PMP>>,
    packed_internal_constants: Vec<__m256i>,
    _phantom: PhantomData<ILP>,
}

impl<FP: FieldParameters, const WIDTH: usize, ILP: InternalLayerParametersAVX2<FP, WIDTH>>
    InternalLayerConstructor<MontyField31<FP>> for Poseidon2InternalLayerMonty31<FP, WIDTH, ILP>
{
    /// Construct an instance of Poseidon2InternalLayerMersenne31AVX2 from a vector containing
    /// the constants for each round. Internally, the constants are transformed into the
    /// {-P, ..., 0} representation instead of the standard {0, ..., P} one.
    fn new_from_constants(internal_constants: Vec<MontyField31<FP>>) -> Self {
        let packed_internal_constants = internal_constants
            .iter()
            .map(|constant| convert_to_vec_neg_form::<FP>(constant.value as i32))
            .collect();
        Self {
            internal_constants,
            packed_internal_constants,
            _phantom: PhantomData,
        }
    }
}

/// The external layers of the Poseidon2 permutation for Monty31 fields.
///
/// The packed constants are stored in negative form as this allows some optimizations.
/// This means given a constant `x`, we treat it as an `i32` and
/// pack 8 copies of `x - P` into the corresponding `__m256i` packed constant.
#[derive(Debug, Clone)]
pub struct Poseidon2ExternalLayerMonty31<PMP: PackedMontyParameters, const WIDTH: usize> {
    pub(crate) external_constants: ExternalLayerConstants<MontyField31<PMP>, WIDTH>,
    packed_initial_external_constants: Vec<[__m256i; WIDTH]>,
    packed_terminal_external_constants: Vec<[__m256i; WIDTH]>,
}

impl<FP: FieldParameters, const WIDTH: usize> ExternalLayerConstructor<MontyField31<FP>, WIDTH>
    for Poseidon2ExternalLayerMonty31<FP, WIDTH>
{
    /// Construct an instance of Poseidon2ExternalLayerMersenne31AVX2 from an array of
    /// vectors containing the constants for each round. Internally, the constants
    ///  are transformed into the {-P, ..., 0} representation instead of the standard {0, ..., P} one.
    fn new_from_constants(
        external_constants: ExternalLayerConstants<MontyField31<FP>, WIDTH>,
    ) -> Self {
        let packed_initial_external_constants = external_constants
            .get_initial_constants()
            .iter()
            .map(|array| array.map(|constant| convert_to_vec_neg_form::<FP>(constant.value as i32)))
            .collect();
        let packed_terminal_external_constants = external_constants
            .get_terminal_constants()
            .iter()
            .map(|array| array.map(|constant| convert_to_vec_neg_form::<FP>(constant.value as i32)))
            .collect();
        Self {
            external_constants,
            packed_initial_external_constants,
            packed_terminal_external_constants,
        }
    }
}

/// Use hard coded methods to compute `x -> x^D` for the even index entries and small `D`.
/// Inputs should be signed 32-bit integers in `[-P, ..., P]`.
/// Outputs will also be signed integers in `(-P, ..., P)` stored in the odd indices.
///
/// # Panics
/// This function will panic if `D` is not `3, 5` or `7`.
#[inline(always)]
#[must_use]
fn exp_small<PMP: PackedMontyParameters, const D: u64>(val: __m256i) -> __m256i {
    match D {
        3 => packed_exp_3::<PMP>(val),
        5 => packed_exp_5::<PMP>(val),
        7 => packed_exp_7::<PMP>(val),
        _ => panic!("No exp function for given D"),
    }
}

/// Compute val -> (val + rc)^D. Each entry of val should be represented in canonical form.
/// Each entry of rc should be represented by an element in [-P, 0].
/// Each entry of the output will be represented by an element in canonical form.
/// If the inputs do not conform to this representation, the result is undefined.
#[inline(always)]
fn add_rc_and_sbox<PMP: PackedMontyParameters, const D: u64>(
    val: &mut PackedMontyField31AVX2<PMP>,
    rc: __m256i,
) {
    unsafe {
        // As our exponential functions simply assume that
        // the input lies in [-P, P] we do not need to perform a reduction provided
        // rc is represented by an element in [-P, 0]
        let vec_val = val.to_vector();
        let val_plus_rc = x86_64::_mm256_add_epi32(vec_val, rc);
        let output = apply_func_to_even_odd::<PMP>(val_plus_rc, exp_small::<PMP, D>);

        *val = PackedMontyField31AVX2::<PMP>::from_vector(output)
    }
}

/// A trait containing the specific information needed to
/// implement the Poseidon2 Permutation for Monty31 Fields.
pub trait InternalLayerParametersAVX2<PMP: PackedMontyParameters, const WIDTH: usize>:
    Clone + Sync
{
    type ArrayLike: AsMut<[__m256i]>;

    // diagonal_mul and add_sum morally should be one function but are split because diagonal_mul can happen simultaneously to
    // the sbox being applied to the first element of the state which is advantageous as this s-box has very high latency.
    // However these functions should only ever be used together and we only make safety guarantees about the output
    // of the combined function add_sum(diagonal_mul(state), sum) which will output field elements
    // in canonical form provided inputs are in canonical form.

    // For these reason we mark both functions as unsafe.

    // All 4 implementation of this trait (Field = BabyBear/KoalaBear, WIDTH = 16/24) have a similarly structured
    // diagonal matrix. The first 9 elements of this matrix are always: [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4] and the remainder
    // are all positive or negative inverse powers of two. This common structure lets us write some default implementations.

    /// # Safety
    ///
    /// This function assumes its output is piped directly into `add_sum`.
    ///
    /// It might not output field elements in canonical form and indeed may even
    /// output incorrect values in places where it is efficient to correct for
    /// the computation in `add_sum`. For example it might output `3*x` instead of `-3*x`
    /// and have `add_sum` compute `sum - x` instead of `x + sum`.
    #[inline(always)]
    unsafe fn diagonal_mul(input: &mut Self::ArrayLike) {
        unsafe {
            Self::diagonal_mul_first_eight(input); // This only affects the first 8 elements.

            Self::diagonal_mul_remainder(input); // This leaves the first 8 elements unchanged.
        }
    }

    /// # Safety
    ///
    /// Multiply the first 8 elements of input by the vector `[1, 2, 1/2, 3, 4, 1/2, 3, 4]`.
    ///
    /// In all implementations of this trait, the first 9 elements of the diagonal matrix are
    /// `[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4]`. The -2 is handled separately and this function handles
    /// the remainder. Note that for the last three elements we multiply by `1/2, 3, 4` and not
    /// `-1/2, -3, -4`. Hence the value in this location will be the negative of what is desired.
    /// This will be handled by `add_sum` and so it is important these elements are not touched
    /// before input is passed into `add_sum`.
    #[inline(always)]
    unsafe fn diagonal_mul_first_eight(input: &mut Self::ArrayLike) {
        let input = input.as_mut();
        // The first 5 elements should be multiplied by: 1, 2, 1/2, 3, 4

        // input[0] is being multiplied by 1 so we ignore it.

        input[1] = add::<PMP>(input[1], input[1]);
        input[2] = halve_avx2::<PMP>(input[2]);

        let acc3 = add::<PMP>(input[3], input[3]);
        input[3] = add::<PMP>(acc3, input[3]);

        let acc4 = add::<PMP>(input[4], input[4]);
        input[4] = add::<PMP>(acc4, acc4);

        // For the final 3 elements we multiply by 1/2, 3, 4.
        // This gives the negative of the correct answer which
        // will be handled by add_sum().

        input[5] = halve_avx2::<PMP>(input[5]);

        let acc6 = add::<PMP>(input[6], input[6]);
        input[6] = add::<PMP>(acc6, input[6]);

        let acc7 = add::<PMP>(input[7], input[7]);
        input[7] = add::<PMP>(acc7, acc7);
    }

    /// # Safety
    ///
    /// This function must not touch the first 8 elements of input.
    /// It may output values which might not be in canonical form or
    /// will be the negative of the expected value. This will be
    /// handled by `add_sum` so it is important these elements are
    /// not touched before input is passed into `add_sum`.
    unsafe fn diagonal_mul_remainder(input: &mut Self::ArrayLike);

    /// # Safety
    ///
    /// Sum must be in canonical form and input must be exactly the output of `diagonal_mul`.
    /// If either of these does not hold, the result is undefined.
    ///
    /// Morally this function is computing `x -> x + sum` however there are some places where
    /// the output of `diagonal_mul` is the negative of the expected value or not canonical.
    /// It is the job of add_sum to correct for these irregularities. Where the output is negative
    /// we compute `x -> sum - x` instead and when not in canonical form we use `signed_add_avx2`
    /// where acts as add where one input is allowed to lie in `(-P, P)`.
    #[inline(always)]
    unsafe fn add_sum(input: &mut Self::ArrayLike, sum: __m256i) {
        unsafe {
            // Diagonal mul multiplied these by 1, 2, 1/2, 3, 4 so we simply need to add the sum.
            input.as_mut()[..5]
                .iter_mut()
                .for_each(|x| *x = add::<PMP>(sum, *x));

            // Diagonal mul multiplied these by 1/2, 3, 4 instead of -1/2, -3, -4 so we need to subtract instead of adding.
            input.as_mut()[5..8]
                .iter_mut()
                .for_each(|x| *x = sub::<PMP>(sum, *x));

            // Diagonal mul output a signed value in (-P, P) so we need to do a signed add.
            // Note that signed add's parameters are not interchangeable. The first parameter must be positive.
            input.as_mut()[8..]
                .iter_mut()
                .for_each(|x| *x = signed_add_avx2::<PMP>(sum, *x));
        }
    }
}

/// Convert elements from canonical form [0, P) to a negative form in [-P, ..., 0) and copy into a vector.
#[inline(always)]
fn convert_to_vec_neg_form<MP: MontyParameters>(input: i32) -> __m256i {
    let input_sub_p = input - (MP::PRIME as i32);
    unsafe {
        // Safety: If this code got compiled then AVX2 intrinsics are available.
        x86_64::_mm256_set1_epi32(input_sub_p)
    }
}

impl<FP, ILP, const D: u64> InternalLayer<PackedMontyField31AVX2<FP>, 16, D>
    for Poseidon2InternalLayerMonty31<FP, 16, ILP>
where
    FP: FieldParameters,
    ILP: InternalLayerParametersAVX2<FP, 16, ArrayLike = [__m256i; 15]>
        + InternalLayerBaseParameters<FP, 16>,
{
    /// Perform the internal layers of the Poseidon2 permutation on the given state.
    fn permute_state(&self, state: &mut [PackedMontyField31AVX2<FP>; 16]) {
        unsafe {
            // Safety: This return values in canonical form when given values in canonical form.

            /*
                Fix a vector v and let Diag(v) denote the diagonal matrix with diagonal given by v.
                Additionally, let 1 denote the matrix with all elements equal to 1.
                The internal layer consists of an sbox operation then a matrix multiplication by 1 + Diag(v).
                Explicitly the internal layer consists of the following 2 operations:

                s0 -> (s0 + rc)^d
                s -> (1 + Diag(v))s

                Note that this matrix multiplication is implemented as:
                sum = sum_i s_i
                s_i -> sum + s_iv_i.
            */

            let mut internal_state = InternalLayer16::from_packed_field_array(*state);

            self.packed_internal_constants.iter().for_each(|&rc| {
                add_rc_and_sbox::<FP, D>(&mut internal_state.s0, rc); // s0 -> (s0 + rc)^D
                let sum_tail = PackedMontyField31AVX2::<FP>::sum_array::<15>(&transmute::<
                    [__m256i; 15],
                    [PackedMontyField31AVX2<FP>; 15],
                >(
                    internal_state.s_hi,
                )); // Get the sum of all elements other than s0.
                ILP::diagonal_mul(&mut internal_state.s_hi); // si -> vi * si for all i > 0.
                let sum = sum_tail + internal_state.s0; // Get the full sum.
                internal_state.s0 = sum_tail - internal_state.s0; // s0 -> sum - 2*s0 = sum_tail - s0.
                ILP::add_sum(
                    &mut internal_state.s_hi,
                    transmute::<PackedMontyField31AVX2<FP>, __m256i>(sum),
                ); // si -> si + sum for all i > 0.
            });

            // This transformation is safe as the above function returns elements
            // in canonical form when given elements in canonical form.
            *state = InternalLayer16::to_packed_field_array(internal_state);
        }
    }
}

impl<FP, ILP, const D: u64> InternalLayer<PackedMontyField31AVX2<FP>, 24, D>
    for Poseidon2InternalLayerMonty31<FP, 24, ILP>
where
    FP: FieldParameters + RelativelyPrimePower<D>,
    ILP: InternalLayerParametersAVX2<FP, 24, ArrayLike = [__m256i; 23]>
        + InternalLayerBaseParameters<FP, 24>,
{
    /// Perform the internal layers of the Poseidon2 permutation on the given state.
    fn permute_state(&self, state: &mut [PackedMontyField31AVX2<FP>; 24]) {
        unsafe {
            // Safety: This return values in canonical form when given values in canonical form.

            /*
                Fix a vector v and let Diag(v) denote the diagonal matrix with diagonal given by v.
                Additionally, let 1 denote the matrix with all elements equal to 1.
                The internal layer consists of an sbox operation then a matrix multiplication by 1 + Diag(v).
                Explicitly the internal layer consists of the following 2 operations:

                s0 -> (s0 + rc)^d
                s -> (1 + Diag(v))s

                Note that this matrix multiplication is implemented as:
                sum = sum_i s_i
                s_i -> sum + s_iv_i.
            */

            let mut internal_state = InternalLayer24::from_packed_field_array(*state);

            self.packed_internal_constants.iter().for_each(|&rc| {
                add_rc_and_sbox::<FP, D>(&mut internal_state.s0, rc); // s0 -> (s0 + rc)^D
                let sum_tail = PackedMontyField31AVX2::<FP>::sum_array::<23>(&transmute::<
                    [__m256i; 23],
                    [PackedMontyField31AVX2<FP>; 23],
                >(
                    internal_state.s_hi,
                )); // Get the sum of all elements other than s0.
                ILP::diagonal_mul(&mut internal_state.s_hi); // si -> vi * si for all i > 0.
                let sum = sum_tail + internal_state.s0; // Get the full sum.
                internal_state.s0 = sum_tail - internal_state.s0; // s0 -> sum - 2*s0 = sum_tail - s0.
                ILP::add_sum(
                    &mut internal_state.s_hi,
                    transmute::<PackedMontyField31AVX2<FP>, __m256i>(sum),
                ); // si -> si + sum for all i > 0.
            });

            // This transformation is safe as the above function returns elements
            // in canonical form when given elements in canonical form.
            *state = InternalLayer24::to_packed_field_array(internal_state);
        }
    }
}

impl<FP, const D: u64, const WIDTH: usize> ExternalLayer<PackedMontyField31AVX2<FP>, WIDTH, D>
    for Poseidon2ExternalLayerMonty31<FP, WIDTH>
where
    FP: FieldParameters + RelativelyPrimePower<D>,
{
    /// Perform the initial external layers of the Poseidon2 permutation on the given state.
    fn permute_state_initial(&self, state: &mut [PackedMontyField31AVX2<FP>; WIDTH]) {
        external_initial_permute_state(
            state,
            &self.packed_initial_external_constants,
            add_rc_and_sbox::<FP, D>,
            &MDSMat4,
        );
    }

    /// Perform the terminal external layers of the Poseidon2 permutation on the given state.
    fn permute_state_terminal(&self, state: &mut [PackedMontyField31AVX2<FP>; WIDTH]) {
        external_terminal_permute_state(
            state,
            &self.packed_terminal_external_constants,
            add_rc_and_sbox::<FP, D>,
            &MDSMat4,
        );
    }
}
