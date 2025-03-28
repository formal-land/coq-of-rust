use super::ops::{adc, sbb};

/// `lhs += rhs + carry`
#[inline(always)]
pub fn adc_n(lhs: &mut [u64], rhs: &[u64], mut carry: u64) -> u64 {
    for i in 0..lhs.len() {
        (lhs[i], carry) = adc(lhs[i], rhs[i], carry);
    }
    carry
}

/// `lhs -= rhs - borrow`
#[inline(always)]
pub fn sbb_n(lhs: &mut [u64], rhs: &[u64], mut borrow: u64) -> u64 {
    for i in 0..lhs.len() {
        (lhs[i], borrow) = sbb(lhs[i], rhs[i], borrow);
    }
    borrow
}
