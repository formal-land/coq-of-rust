use core::iter::Take;

use crate::{Powers, TwoAdicField};

/// Coset of a subgroup of the group of units of a finite field of order equal
/// to a power of two.
///
/// # Examples
///
/// ```
/// # use p3_field::{
///     TwoAdicField,
///     PrimeCharacteristicRing,
///     coset::TwoAdicMultiplicativeCoset
/// };
/// # use itertools::Itertools;
/// # use p3_baby_bear::BabyBear;
/// #
/// type F = BabyBear;
/// let log_size = 3;
/// let shift = F::from_u64(7);
/// let mut coset = TwoAdicMultiplicativeCoset::new(shift, log_size).unwrap();
/// let generator = coset.subgroup_generator();
///
/// // Coset elements can be queried by index
/// assert_eq!(coset.element(4), shift * generator.exp_u64(4));
///
/// // Coset elements can be iterated over in the canonical order
/// assert_eq!(
///     coset.iter().collect_vec(),
///     (0..1 << log_size).map(|i| shift * generator.exp_u64(i)).collect_vec()
/// );
///
/// // Cosets can be (element-wise) raised to a power of 2, either maintaining
/// // the shift and raising only the subgroup, or raising both.
/// let coset_shrunk_subgroup = coset.shrink_coset(2).unwrap();
/// assert_eq!(
///     coset_shrunk_subgroup.subgroup_generator(),
///     coset.subgroup_generator().exp_power_of_2(2),
/// );
/// assert_eq!(
///     coset_shrunk_subgroup.shift(),
///     coset.shift()
/// );
///
/// let coset_power = coset.exp_power_of_2(2).unwrap();
/// assert_eq!(
///     coset_power.subgroup_generator(),
///     coset.subgroup_generator().exp_power_of_2(2),
/// );
/// assert_eq!(
///     coset_power.shift(),
///     coset.shift().exp_power_of_2(2),
/// );
/// ```
#[derive(Clone, Copy, Debug)]
pub struct TwoAdicMultiplicativeCoset<F: TwoAdicField> {
    // Letting s = shift, and g = generator (of order 2^log_size), the coset in
    // question is
    //     s * <g> = {s, s * g, shift * g^2, ..., s * g^(2^log_size - 1)]
    shift: F,
    log_size: usize,
}

impl<F: TwoAdicField> TwoAdicMultiplicativeCoset<F> {
    /// Returns the coset `shift * <generator>`, where `generator` is a
    /// canonical (i. e. fixed in the implementation of `F: TwoAdicField`)
    /// generator of the unique subgroup of the units of `F` of order `2 ^
    /// log_size`. Returns `None` if `log_size > F::TWO_ADICITY`.
    ///
    /// # Arguments
    ///
    ///  - `shift`: the value by which the subgroup is (multiplicatively)
    ///    shifted
    ///  - `log_size`: the size of the subgroup (and hence of the coset) is `2 ^
    ///    log_size`. This determines the subgroup uniquely.
    pub fn new(shift: F, log_size: usize) -> Option<Self> {
        if log_size <= F::TWO_ADICITY {
            Some(Self { shift, log_size })
        } else {
            None
        }
    }

    /// Returns the generator of the subgroup of order `self.size()`.
    #[inline]
    pub fn subgroup_generator(&self) -> F {
        F::two_adic_generator(self.log_size)
    }

    /// Returns the shift of the coset.
    #[inline]
    pub fn shift(&self) -> F {
        self.shift
    }

    /// Returns the log2 of the size of the coset.
    #[inline]
    pub fn log_size(&self) -> usize {
        self.log_size
    }

    /// Returns the size of the coset.
    #[inline]
    pub fn size(&self) -> usize {
        1 << self.log_size
    }

    /// Returns a new coset with its subgroup reduced by a factor of
    /// `2^log_scale_factor` in size (i. e. with generator equal to the
    /// `2^log_scale_factor`-th power of that of the original coset), leaving
    /// the shift untouched. Note that new coset is contained in the original one.
    /// Returns `None` if `log_scale_factor` is greater than `self.log_size()`.
    pub fn shrink_coset(&self, log_scale_factor: usize) -> Option<Self> {
        self.log_size
            .checked_sub(log_scale_factor)
            .map(|new_log_size| TwoAdicMultiplicativeCoset {
                shift: self.shift,
                log_size: new_log_size,
            })
    }

    /// Returns the coset `self^(2^log_scale_factor)` (i. e. with shift and
    /// subgroup generator equal to the `2^log_scale_factor`-th power of the
    /// original ones). Returns `None` if `log_scale_factor` is greater than `self.log_size()`.
    pub fn exp_power_of_2(&self, log_scale_factor: usize) -> Option<Self> {
        self.shrink_coset(log_scale_factor).map(|mut coset| {
            coset.shift = self.shift.exp_power_of_2(log_scale_factor);
            coset
        })
    }

    /// Returns a new coset of the same size whose shift is equal to `scale * self.shift`.
    pub fn shift_by(&self, scale: F) -> TwoAdicMultiplicativeCoset<F> {
        TwoAdicMultiplicativeCoset {
            shift: self.shift * scale,
            log_size: self.log_size,
        }
    }

    /// Returns a new coset where the shift has been set to `shift`
    pub fn set_shift(&self, shift: F) -> TwoAdicMultiplicativeCoset<F> {
        TwoAdicMultiplicativeCoset {
            shift,
            log_size: self.log_size,
        }
    }

    /// Checks if the given field element is in the coset
    pub fn contains(&self, element: F) -> bool {
        // Note that, in a finite field F (this is not true of a general finite
        // commutative ring), there is exactly one subgroup of |F^*| of order n
        // for each divisor n of |F| - 1, and its elements e are uniquely
        // caracterised by the condition e^n = 1.

        // We check (shift^{-1} * element)^(2^log_size) = 1, which is equivalent
        // to checking shift^(2^log_size) = element^(2^log_size) - this avoids
        // inversion at the cost of a few squarings. The loop terminates early
        // if possible.
        let (mut shift, mut element) = (self.shift, element);

        for _ in 0..self.log_size {
            if element == shift {
                return true;
            }
            element = element.square();
            shift = shift.square();
        }

        element == shift
    }

    /// Returns the element `shift * generator^index`, which is the `index %
    /// self.size()`-th element of `self` (and, in particular, the `index`-th
    /// element of `self` whenever `index` < self.size()).
    #[inline]
    pub fn element(&mut self, index: usize) -> F {
        self.shift * self.generator_exp(index)
    }

    // Internal function which computes `generator^exp`. It uses the
    // square-and-multiply algorithm with the caveat that squares of the
    // generator are queried from the field (which typically should have them
    // stored), i. e. rather "fetch-and-multiply".
    fn generator_exp(&self, exp: usize) -> F {
        let mut gen_power = F::ONE;
        // As `generator` satisfies `generator^{self.size()} == 1` we can replace `exp` by `exp mod self.size()`.
        // As `self.size()` is a power of `2` this can be done with an `&` instead of a `%`.
        let mut exp = exp & (self.size() - 1);
        let mut i = self.log_size();

        while exp > 0 {
            if exp & 1 != 0 {
                gen_power *= F::two_adic_generator(i);
            }
            exp >>= 1;

            i -= 1;
        }

        gen_power
    }

    /// Returns an iterator over the elements of the coset in the canonical order
    /// `shift * generator^0, shift * generator^1, ...,
    /// shift * generator^(2^log_size - 1)`.
    pub fn iter(&self) -> Take<Powers<F>> {
        self.subgroup_generator()
            .shifted_powers(self.shift)
            .take(1 << self.log_size)
    }
}

impl<F: TwoAdicField> IntoIterator for TwoAdicMultiplicativeCoset<F> {
    type Item = F;
    type IntoIter = Take<Powers<F>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
