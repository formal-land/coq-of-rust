//! A collection of traits and macros which convert primitive integer types into field elements.

/// A macro which lets us define the function `from_Int`
/// where `Int` can be replaced by any integer type.
///
/// Running, `from_integer_types!(Int)` adds the following code to a trait:
///
/// ```rust,ignore
/// /// Given an integer `r`, return the sum of `r` copies of `ONE`:
/// ///
/// /// `r * Self::ONE =  Self::ONE + ... + Self::ONE (r times)`.
/// ///
/// /// Note that the output only depends on `r mod p`.
/// ///
/// /// This should be avoided in performance critical locations.
/// fn from_Int(int: Int) -> Self {
///     Self::from_prime_subfield(Self::PrimeSubfield::from_int(int))
/// }
/// ```
///
/// This macro can be run for any `Int` where `Self::PrimeSubfield` implements `QuotientMap<Int>`.
/// It considerably cuts down on the amount of copy/pasted code.
macro_rules! from_integer_types {
    ($($type:ty),* $(,)? ) => {
        $( paste::paste!{
            /// Given an integer `r`, return the sum of `r` copies of `ONE`:
            ///
            /// `r * Self::ONE =  Self::ONE + ... + Self::ONE (r times)`.
            ///
            /// Note that the output only depends on `r mod p`.
            ///
            /// This should be avoided in performance critical locations.
            fn [<from_ $type>](int: $type) -> Self {
                Self::from_prime_subfield(Self::PrimeSubfield::from_int(int))
            }
        }
        )*
    };
}

/// Implementation of the quotient map `ℤ -> ℤ/p` which sends an integer `r` to its conjugacy class `[r]`.
///
/// This is the key trait allowing us to convert integers into field elements. Each prime field
/// should implement this for all primitive integer types.
pub trait QuotientMap<Int>: Sized {
    /// Convert a given integer into an element of the field `ℤ/p`.
    ///
    /// This is the most generic method which makes no assumptions on the size of the input.
    /// Where possible, this method should be used with the smallest possible integer type.
    /// For example, if a 32-bit integer `x` is known to be less than `2^16`, then
    /// `from_int(x as u16)` will often be faster than `from_int(x)`.
    ///
    /// This method is also strongly preferred over `from_canonical_checked/from_canonical_unchecked`.
    /// It will usually be identical when `Int` is a small type, e.g. `u8/u16` and is safer for
    /// larger types.
    fn from_int(int: Int) -> Self;

    /// Convert a given integer into an element of the field `ℤ/p`. The input is checked to
    /// ensure it lies within a given range.
    /// - If `Int` is an unsigned integer type the input must lie in `[0, p - 1]`.
    /// - If `Int` is a signed integer type the input must lie in `[-(p - 1)/2, (p - 1)/2]`.
    ///
    /// Return `None` if the input lies outside this range and `Some(val)` otherwise.
    fn from_canonical_checked(int: Int) -> Option<Self>;

    /// Convert a given integer into an element of the field `ℤ/p`. The input is guaranteed
    /// to lie within a specific range depending on `p`. If the input lies outside of this
    /// range, the output is undefined.
    ///
    /// In general `from_canonical_unchecked` will be faster for either `signed` or `unsigned`
    /// types but the specifics will depend on the field.
    ///
    /// # Safety
    /// - If `Int` is an unsigned integer type then the allowed range will include `[0, p - 1]`.
    /// - If `Int` is a signed integer type then the allowed range will include `[-(p - 1)/2, (p - 1)/2]`.
    unsafe fn from_canonical_unchecked(int: Int) -> Self;
}

/// This allows us to avoid some duplication which arises when working with fields which contain a generic parameter.
///
/// See `quotient_map_small_int` to see what this will expand to/how to call it. This is not intended for use outside of
/// that macro.
#[macro_export]
macro_rules! quotient_map_small_internals {
    ($field:ty, $field_size:ty, $small_int:ty) => {
        #[doc = concat!("Convert a given `", stringify!($small_int), "` integer into an element of the `", stringify!($field), "` field.
        \n Due to the integer type, the input value is always canonical.")]
        #[inline]
        fn from_int(int: $small_int) -> Self {
            // Should be removed by the compiler.
            assert!(size_of::<$small_int>() < size_of::<$field_size>());
            unsafe {
                Self::from_canonical_unchecked(int as $field_size)
            }
        }

        #[doc = concat!("Convert a given `", stringify!($small_int), "` integer into an element of the `", stringify!($field), "` field.
        \n Due to the integer type, the input value is always canonical.")]
        #[inline]
        fn from_canonical_checked(int: $small_int) -> Option<Self> {
            // Should be removed by the compiler.
            assert!(size_of::<$small_int>() < size_of::<$field_size>());
            Some(unsafe {
                Self::from_canonical_unchecked(int as $field_size)
            })
        }

        #[doc = concat!("Convert a given `", stringify!($small_int), "` integer into an element of the `", stringify!($field), "` field.
        \n Due to the integer type, the input value is always canonical.")]
        #[inline]
        unsafe fn from_canonical_unchecked(int: $small_int) -> Self {
            // We use debug_assert to ensure this is removed by the compiler in release mode.
            debug_assert!(size_of::<$small_int>() < size_of::<$field_size>());
            unsafe {
                Self::from_canonical_unchecked(int as $field_size)
            }
        }
    };
}

/// If the integer type is smaller than the field order all possible inputs are canonical.
/// In such a case we can easily implement `QuotientMap<SmallInt>` as all three methods will coincide.
///
/// The range of acceptable integer types depends on the size of the field:
/// - For 31 bit fields, `SmallInt = u8, u16, i8, i16`.
/// - For 64 bit fields, `SmallInt = u8, u16, u32, i8, i16, i32`.
/// - For large fields (E.g. `Bn254`), `SmallInt` can be anything except for the largest primitive integer type `u128/i128`
///
/// This macro accepts 3 inputs.
/// - The name of the prime field `P`
/// - The larger integer type `Int` which inputs should be cast to.
/// - A list of smaller integer types to auto implement `QuotientMap<SmallInt>`.
///
/// Then `from_int`, `from_canonical_checked`, `from_canonical_unchecked` are all
/// implemented by casting the input to an `Int` and using the `from_canonical_unchecked`
/// method from `QuotientMap<Int>`.
///
/// For a concrete example, `quotient_map_small_int!(Mersenne31, u32, [u8])` produces the following code:
///
/// ```rust,ignore
/// impl QuotientMap<u8> for Mersenne31 {
///     /// Convert a given `u8` integer into an element of the `Mersenne31` field.
///     ///
///     /// Due to the integer type, the input value is always canonical.
///     #[inline]
///     fn from_int(int: u8) -> Mersenne31 {
///         // Should be removed by the compiler.
///         assert!(size_of::<u8>() < size_of::<u32>());
///         unsafe {
///             Self::from_canonical_unchecked(int as u32)
///         }
///     }
///
///     /// Convert a given `u8` integer into an element of the `Mersenne31` field.
///     ///
///     /// Due to the integer type, the input value is always canonical.
///     #[inline]
///     fn from_canonical_checked(int: u8) -> Option<Mersenne31> {
///         // Should be removed by the compiler.
///         assert!(size_of::<u8>() < size_of::<u32>());
///         Some(unsafe {
///             Self::from_canonical_unchecked(int as u32)
///         })
///     }
///
///     /// Convert a given `u8` integer into an element of the `Mersenne31` field.
///     ///
///     /// Due to the integer type, the input value is always canonical.
///     #[inline]
///     unsafe fn from_canonical_unchecked(int: u8) -> Mersenne31 {
///         // We use debug_assert to ensure this is removed by the compiler in release mode.
///         debug_assert!(size_of::<u8>() < size_of::<u32>());
///         unsafe {
///             Self::from_canonical_unchecked(int as u32)
///         }
///     }
/// }
///```
///
/// Fields will often use this method twice. Once for unsigned ints and once for signed ints.
///
/// We need two slightly different versions for this macro as MontyField31 uses generic parameters.
#[macro_export]
macro_rules! quotient_map_small_int {
    ($field:ty, $field_size:ty, [$($small_int:ty),*] ) => {
        $(
        paste::paste!{
            impl QuotientMap<$small_int> for $field {
                $crate::quotient_map_small_internals!($field, $field_size, $small_int);
            }
        }
        )*
    };

    ($field:ty, $field_size:ty, $field_param:ty, [$($small_int:ty),*] ) => {
        $(
        paste::paste!{
            impl<FP: $field_param> QuotientMap<$small_int> for $field<FP> {
                $crate::quotient_map_small_internals!($field, $field_size, $small_int);
            }
        }
        )*
    };
}

/// If the unsigned integer type is large enough, there is often no method better for `from_int` than
/// just doing a modular reduction to a smaller type.
///
/// This macro accepts 6 inputs.
/// - The name of the prime field `P`
/// - The smallest natural integer type large enough to contain the field characteristic.
/// - The characteristic of the field.
/// - A string giving the range for which from_canonical_checked produces the correct result.
/// - A string giving the range for which from_canonical_unchecked produces the correct result.
/// - A list of large integer types to auto implement `QuotientMap<LargeInt>`.
///
/// For a concrete example, `quotient_map_large_uint!(Mersenne31, u32, Mersenne31::ORDER_U32, "`\[0, 2^31 - 2\]`", "`\[0, 2^31 - 1\]`", [u128])` would produce the following code:
///
/// ```rust,ignore
/// impl QuotientMap<u128> for Mersenne31 {
///     /// Convert a given `u128` integer into an element of the `Mersenne31` field.
///     ///
///     /// Uses a modular reduction to reduce to canonical form.
///     /// This should be avoided in performance critical locations.
///     #[inline]
///     fn from_int(int: u128) -> Mersenne31 {
///         // Should be removed by the compiler.
///         assert!(size_of::<u128>() > size_of::<u32>());
///         let red = (int % (Mersenne31::ORDER_U32 as u128)) as u32;
///            unsafe {
///                // This is safe as red is less than the field order by assumption.
///                Self::from_canonical_unchecked(red)
///            }
///     }
///
///     /// Convert a given `u128` integer into an element of the `Mersenne31` field.
///     ///
///     /// Returns `None` if the input does not lie in the range: [0, 2^31 - 2].
///     #[inline]
///     fn from_canonical_checked(int: u128) -> Option<Mersenne31> {
///         if int < Mersenne31::ORDER_U32 as u128 {
///             unsafe {
///                 // This is safe as we just checked that int is less than the field order.
///                 Some(Self::from_canonical_unchecked(int as u32))
///             }
///         } else {
///             None
///         }
///     }
///
///     /// Convert a given `u128` integer into an element of the `Mersenne31` field.
///     ///
///     /// # Safety
///     /// The input must lie in the range:", [0, 2^31 - 1].
///     #[inline]
///     unsafe fn from_canonical_unchecked(int: u128) -> Mersenne31 {
///         unsafe {
///             Self::from_canonical_unchecked(int as u32)
///         }
///     }
/// }
///```
#[macro_export]
macro_rules! quotient_map_large_uint {
    ($field:ty, $field_size:ty, $field_order:expr, $checked_bounds:literal, $unchecked_bounds:literal, [$($large_int:ty),*] ) => {
        $(
        impl QuotientMap<$large_int> for $field {
            #[doc = concat!("Convert a given `", stringify!($large_int), "` integer into an element of the `", stringify!($field), "` field.
                \n Uses a modular reduction to reduce to canonical form. \n This should be avoided in performance critical locations.")]
            #[inline]
            fn from_int(int: $large_int) -> $field {
                assert!(size_of::<$large_int>() > size_of::<$field_size>());
                let red = (int % ($field_order as $large_int)) as $field_size;
                unsafe {
                    // This is safe as red is less than the field order by assumption.
                    Self::from_canonical_unchecked(red)
                }
            }

            #[doc = concat!("Convert a given `", stringify!($large_int), "` integer into an element of the `", stringify!($field), "` field.
                \n Returns `None` if the input does not lie in the range:", $checked_bounds, ".")]
            #[inline]
            fn from_canonical_checked(int: $large_int) -> Option<$field> {
                if int < $field_order as $large_int {
                    unsafe {
                        // This is safe as we just checked that int is less than the field order.
                        Some(Self::from_canonical_unchecked(int as $field_size))
                    }
                } else {
                    None
                }
            }

            #[doc = concat!("Convert a given `", stringify!($large_int), "` integer into an element of the `", stringify!($field), "` field.")]
            ///
            /// # Safety
            #[doc = concat!("The input must lie in the range:", $unchecked_bounds, ".")]
            #[inline]
            unsafe fn from_canonical_unchecked(int: $large_int) -> $field {
                unsafe {
                    Self::from_canonical_unchecked(int as $field_size)
                }
            }
        }
        )*
    };
}

/// For large signed integer types, a simple method which is usually good enough is to simply check the sign and use this to
/// pass to the equivalent unsigned method.
///
/// This will often not be the fastest implementation but should be good enough for most cases.
///
/// This macro accepts 4 inputs.
/// - The name of the prime field `P`.
/// - The smallest natural integer type large enough to contain the field characteristic.
/// - A string giving the range for which from_canonical_checked produces the correct result.
/// - A string giving the range for which from_canonical_unchecked produces the correct result.
/// - A list of pairs of large sign and unsigned integer types to auto implement `QuotientMap<LargeSignInt>`.
///
/// For a concrete example, `quotient_map_large_iint!(Mersenne31, i32, "`\[-2^30, 2^30\]`", "`\[1 - 2^31, 2^31 - 1\]`", [(i128, u128)])` would produce the following code:
///
/// ```rust,ignore
/// impl QuotientMap<i128> for Mersenne31 {
///     /// Convert a given `i128` integer into an element of the `Mersenne31` field.
///     ///
///     /// This checks the sign and then makes use of the equivalent method for unsigned integers.
///     /// This should be avoided in performance critical locations.
///     #[inline]
///     fn from_int(int: i128) -> Mersenne31 {
///         if int >= 0 {
///             Self::from_int(int as u128)
///         } else {
///            -Self::from_int(-int as u128)
///         }
///     }
///
///     /// Convert a given `i128` integer into an element of the `Mersenne31` field.
///     ///
///     /// Returns `None` if the input does not lie in the range: `[-2^30, 2^30]`.
///     #[inline]
///     fn from_canonical_checked(int: i128) -> Option<Mersenne31> {
///         // We just check that int fits into an i32 now and then use the i32 method.
///         let int_small = TryInto::<i32>::try_into(int);
///         if int_small.is_ok() {
///             Self::from_canonical_checked(int_small.unwrap())
///         } else {
///             None
///         }
///     }
///
///     /// Convert a given `i128` integer into an element of the `Mersenne31` field.
///     ///
///     /// # Safety
///     /// The input must lie in the range:", `[1 - 2^31, 2^31 - 1]`.
///     #[inline]
///     unsafe fn from_canonical_unchecked(int: i128) -> Mersenne31 {
///         unsafe {
///             Self::from_canonical_unchecked(int as i32)
///         }
///     }
/// }
///```
#[macro_export]
macro_rules! quotient_map_large_iint {
    ($field:ty, $field_size:ty, $checked_bounds:literal, $unchecked_bounds:literal, [$(($large_signed_int:ty, $large_int:ty)),*] ) => {
        $(
        impl QuotientMap<$large_signed_int> for $field {
            #[doc = concat!("Convert a given `", stringify!($large_signed_int), "` integer into an element of the `", stringify!($field), "` field.
                \n This checks the sign and then makes use of the equivalent method for unsigned integers. \n This should be avoided in performance critical locations.")]
            #[inline]
            fn from_int(int: $large_signed_int) -> $field {
                if int >= 0 {
                    Self::from_int(int as $large_int)
                } else {
                    -Self::from_int(-int as $large_int)
                }
            }

            #[doc = concat!("Convert a given `", stringify!($large_int), "` integer into an element of the `", stringify!($field), "` field.
                \n Returns `None` if the input does not lie in the range:", $checked_bounds, ".")]
            #[inline]
            fn from_canonical_checked(int: $large_signed_int) -> Option<$field> {
                let int_small = TryInto::<$field_size>::try_into(int).ok();

                // The type of the following is Option<Option<$field>>.
                // We use the ? operator to convert it to Option<$field>, with
                // None and Some(None) both becoming None.
                int_small.map(Self::from_canonical_checked)?
            }

            #[doc = concat!("Convert a given `", stringify!($large_int), "` integer into an element of the `", stringify!($field), "` field.")]
            ///
            /// # Safety
            #[doc = concat!("The input must lie in the range:", $unchecked_bounds, ".")]
            #[inline]
            unsafe fn from_canonical_unchecked(int: $large_signed_int) -> $field {
                unsafe {
                    Self::from_canonical_unchecked(int as $field_size)
                }
            }
        }
        )*
    };
}

/// We implement `QuotientMap<usize>` (`QuotientMap<isize>`) by matching against the size of `usize` (`isize`)
/// and then converting `usize` (`isize`) into the equivalent matching integer type.
///
/// The code is identical for both `usize` and `isize` outside of replacing some u's by i's so we use a macro
/// to avoid the copy and paste.
macro_rules! impl_u_i_size {
    ($intsize:ty, $int8:ty, $int16:ty, $int32:ty, $int64:ty, $int128:ty) => {
        impl<
                F: QuotientMap<$int8>
                    + QuotientMap<$int16>
                    + QuotientMap<$int32>
                    + QuotientMap<$int64>
                    + QuotientMap<$int128>,
            > QuotientMap<$intsize> for F
        {
            #[doc = concat!("We use the `from_int` method of the primitive integer type identical to `", stringify!($intsize), "` on this machine")]
            fn from_int(int: $intsize) -> Self {
                match size_of::<$intsize>() {
                    1 => Self::from_int(int as $int8),
                    2 => Self::from_int(int as $int16),
                    4 => Self::from_int(int as $int32),
                    8 => Self::from_int(int as $int64),
                    16 => Self::from_int(int as $int128),
                    _ => unreachable!(concat!(stringify!($intsize), "is not equivalent to any primitive integer types.")),
                }
            }

            #[doc = concat!("We use the `from_canonical_checked` method of the primitive integer type identical to `", stringify!($intsize), "` on this machine")]
            fn from_canonical_checked(int: $intsize) -> Option<Self> {
                match size_of::<$intsize>() {
                    1 => Self::from_canonical_checked(int as $int8),
                    2 => Self::from_canonical_checked(int as $int16),
                    4 => Self::from_canonical_checked(int as $int32),
                    8 => Self::from_canonical_checked(int as $int64),
                    16 => Self::from_canonical_checked(int as $int128),
                    _ => unreachable!(concat!(stringify!($intsize), " is not equivalent to any primitive integer types.")),
                }
            }

            #[doc = concat!("We use the `from_canonical_unchecked` method of the primitive integer type identical to `", stringify!($intsize), "` on this machine")]
            unsafe fn from_canonical_unchecked(int: $intsize) -> Self {
                unsafe {
                    match size_of::<$intsize>() {
                        1 => Self::from_canonical_unchecked(int as $int8),
                        2 => Self::from_canonical_unchecked(int as $int16),
                        4 => Self::from_canonical_unchecked(int as $int32),
                        8 => Self::from_canonical_unchecked(int as $int64),
                        16 => Self::from_canonical_unchecked(int as $int128),
                        _ => unreachable!(concat!(stringify!($intsize), " is not equivalent to any primitive integer types.")),
                    }
                }
            }
        }
    };
}

impl_u_i_size!(usize, u8, u16, u32, u64, u128);
impl_u_i_size!(isize, i8, i16, i32, i64, i128);

// The only general type for which we do not provide a macro is for large signed integers.
// This is because different field will usually want to handle large signed integers in
// their own way.
pub(crate) use from_integer_types;
pub use {quotient_map_large_iint, quotient_map_large_uint, quotient_map_small_int};
