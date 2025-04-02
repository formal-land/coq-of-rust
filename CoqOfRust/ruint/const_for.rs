/// Compile time for loops with a `const` variable for testing.
///
/// Repeats a block of code with different values assigned to a constant.
///
/// ```rust
/// # use ruint::{const_for, nlimbs, Uint};
/// const_for!(BITS in [0, 10, 100] {
///     const LIMBS: usize = nlimbs(BITS);
///     println!("{:?}", Uint::<BITS, LIMBS>::MAX);
/// });
/// ```
///
/// is equivalent to
///
/// ```rust
/// # use ruint::{const_for, Uint};
/// println!("{:?}", Uint::<0, 0>::MAX);
/// println!("{:?}", Uint::<10, 1>::MAX);
/// println!("{:?}", Uint::<100, 2>::MAX);
/// ```
///
/// It comes with two built-in lists: `NON_ZERO` which is equivalent to
///
/// ```text
/// [1, 2, 63, 64, 65, 127, 128, 129, 256, 384, 512, 4096]
/// ```
///
/// and `SIZES` which is the same but also has `0` as a value.
///
/// In combination with [`proptest!`][proptest::proptest] this allows for
/// testing over a large range of [`Uint`][crate::Uint] types and values:
///
/// ```rust
/// # use proptest::prelude::*;
/// # use ruint::{const_for, nlimbs, Uint};
/// const_for!(BITS in SIZES {
///    const LIMBS: usize = nlimbs(BITS);
///    proptest!(|(value: Uint<BITS, LIMBS>)| {
///         // ... test code
///     });
/// });
/// ```
#[macro_export]
macro_rules! const_for {
    ($C:ident in [ $( $n:literal ),* ] $x:block) => {
        $({
            const $C: usize = $n;
            $x
        })*
    };
    ($C:ident in SIZES $x:block) => {
        $crate::const_for!($C in [0] $x);
        $crate::const_for!($C in NON_ZERO $x);
    };
    ($C:ident in NON_ZERO $x:block) => {
        $crate::const_for!($C in [1, 2, 63, 64, 65, 127, 128, 129, 256, 384, 512, 4096] $x);
    };
    ($C:ident in BENCH $x:block) => {
        $crate::const_for!($C in [0, 64, 128, 192, 256, 384, 512, 4096] $x);
    };
    ($C:ident in $S:ident if ( $c:expr ) $x:block) => {
        $crate::const_for!($C in $S {
            if $c {
                $x
            }
        });
    };
}
