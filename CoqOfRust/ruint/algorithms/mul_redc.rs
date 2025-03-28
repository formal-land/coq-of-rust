use super::addmul;
use core::iter::zip;

/// See Handbook of Applied Cryptography, Algorithm 14.32, p. 601.
#[allow(clippy::cognitive_complexity)] // REFACTOR: Improve
#[inline]
pub fn mul_redc(a: &[u64], b: &[u64], result: &mut [u64], m: &[u64], inv: u64) {
    debug_assert!(!m.is_empty());
    debug_assert_eq!(a.len(), m.len());
    debug_assert_eq!(b.len(), m.len());
    debug_assert_eq!(result.len(), m.len());
    debug_assert_eq!(inv.wrapping_mul(m[0]), u64::MAX);

    // Compute temp full product.
    // OPT: Do combined multiplication and reduction.
    let mut temp = vec![0; 2 * m.len() + 1];
    addmul(&mut temp, a, b);

    // Reduce temp.
    for i in 0..m.len() {
        let u = temp[i].wrapping_mul(inv);

        // REFACTOR: Create add_mul1 routine.
        let mut carry = 0;
        #[allow(clippy::cast_possible_truncation)] // Intentional
        for j in 0..m.len() {
            carry += u128::from(temp[i + j]) + u128::from(m[j]) * u128::from(u);
            temp[i + j] = carry as u64;
            carry >>= 64;
        }
        #[allow(clippy::cast_possible_truncation)] // Intentional
        for j in m.len()..(temp.len() - i) {
            carry += u128::from(temp[i + j]);
            temp[i + j] = carry as u64;
            carry >>= 64;
        }
        debug_assert!(carry == 0);
    }
    debug_assert!(temp[temp.len() - 1] <= 1); // Basically a carry flag.

    // Copy result.
    result.copy_from_slice(&temp[m.len()..2 * m.len()]);

    // Subtract one more m if result >= m
    let mut reduce = true;
    // REFACTOR: Create cmp routine
    if temp[temp.len() - 1] == 0 {
        for (r, m) in zip(result.iter().rev(), m.iter().rev()) {
            if r < m {
                reduce = false;
                break;
            }
            if r > m {
                break;
            }
        }
    }
    if reduce {
        // REFACTOR: Create sub routine
        let mut carry = 0;
        #[allow(clippy::cast_possible_truncation)] // Intentional
        #[allow(clippy::cast_sign_loss)] // Intentional
        for (r, m) in zip(result.iter_mut(), m.iter().copied()) {
            carry += i128::from(*r) - i128::from(m);
            *r = carry as u64;
            carry >>= 64; // Sign extending shift
        }
        debug_assert!(carry == 0 || temp[temp.len() - 1] == 1);
    }
}
