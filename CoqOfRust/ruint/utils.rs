#[cfg(feature = "alloc")]
#[allow(unused_imports)]
use alloc::vec::Vec;

/// Like `a % b` but returns `b` instead of `0`.
#[allow(dead_code)] // This is used by some support features.
#[must_use]
pub(crate) const fn rem_up(a: usize, b: usize) -> usize {
    let rem = a % b;
    if rem > 0 {
        rem
    } else {
        b
    }
}

#[allow(dead_code)] // This is used by some support features.
#[inline]
fn last_idx<T: PartialEq>(x: &[T], value: &T) -> usize {
    x.iter().rposition(|b| b != value).map_or(0, |idx| idx + 1)
}

#[allow(dead_code)] // This is used by some support features.
#[inline]
#[must_use]
pub(crate) fn trim_end_slice<'a, T: PartialEq>(slice: &'a [T], value: &T) -> &'a [T] {
    &slice[..last_idx(slice, value)]
}

#[cfg(feature = "alloc")]
#[inline]
pub(crate) fn trim_end_vec<T: PartialEq>(vec: &mut Vec<T>, value: &T) {
    vec.truncate(last_idx(vec, value));
}

// Branch prediction hints.
#[cfg(feature = "nightly")]
pub(crate) use core::intrinsics::{likely, unlikely};

#[cfg(not(feature = "nightly"))]
pub(crate) use core::convert::identity as likely;
#[cfg(not(feature = "nightly"))]
pub(crate) use core::convert::identity as unlikely;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trim() {
        assert_eq!(trim_end_slice(&[], &0), &[] as &[i32]);
        assert_eq!(trim_end_slice(&[0], &0), &[] as &[i32]);
        assert_eq!(trim_end_slice(&[0, 1], &0), &[0, 1]);
        assert_eq!(trim_end_slice(&[0, 1, 0], &0), &[0, 1]);
        assert_eq!(trim_end_slice(&[0, 1, 0, 0], &0), &[0, 1]);
        assert_eq!(trim_end_slice(&[0, 1, 0, 0, 0], &0), &[0, 1]);
        assert_eq!(trim_end_slice(&[0, 1, 0, 1, 0], &0), &[0, 1, 0, 1]);

        let trim_end_vec = |mut v: Vec<i32>, x: &i32| {
            trim_end_vec(&mut v, x);
            v
        };
        assert_eq!(trim_end_vec(vec![], &0), &[] as &[i32]);
        assert_eq!(trim_end_vec(vec![0], &0), &[] as &[i32]);
        assert_eq!(trim_end_vec(vec![0, 1], &0), &[0, 1]);
        assert_eq!(trim_end_vec(vec![0, 1, 0], &0), &[0, 1]);
        assert_eq!(trim_end_vec(vec![0, 1, 0, 0], &0), &[0, 1]);
        assert_eq!(trim_end_vec(vec![0, 1, 0, 0, 0], &0), &[0, 1]);
        assert_eq!(trim_end_vec(vec![0, 1, 0, 1, 0], &0), &[0, 1, 0, 1]);
    }
}
