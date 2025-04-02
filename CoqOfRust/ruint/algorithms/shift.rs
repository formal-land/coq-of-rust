#[inline(always)]
pub fn shift_left_small(limbs: &mut [u64], amount: usize) -> u64 {
    debug_assert!(amount < 64);
    let mut overflow = 0;
    for limb in limbs {
        let value = (*limb << amount) | overflow;
        overflow = *limb >> (64 - amount);
        *limb = value;
    }
    overflow
}

#[inline(always)]
pub fn shift_right_small(limbs: &mut [u64], amount: usize) -> u64 {
    debug_assert!(amount < 64);

    let mut overflow = 0;
    for limb in limbs.iter_mut().rev() {
        let value = (*limb >> amount) | overflow;
        overflow = *limb << (64 - amount);
        *limb = value;
    }
    overflow
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shift_left_small() {
        let mut limbs = [0x1234_5678_9abc_def0, 0x1234_5678_9abc_def0];
        let overflow = shift_left_small(&mut limbs, 4);
        assert_eq!(limbs, [0x2345_6789_abcd_ef00, 0x2345_6789_abcd_ef01]);
        assert_eq!(overflow, 0x1);
    }

    #[test]
    fn test_shift_right_small() {
        let mut limbs = [0x1234_5678_9abc_deff, 0x1234_5678_9abc_def0];
        let overflow = shift_right_small(&mut limbs, 4);
        assert_eq!(limbs, [0x0123_4567_89ab_cdef, 0x0123_4567_89ab_cdef]);
        assert_eq!(overflow, 0xf << 60);
    }
}
