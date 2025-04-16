use core::mem::MaybeUninit;

use itertools::izip;
use p3_field::{Field, PackedField, PackedValue};

pub trait Butterfly<F: Field>: Copy + Send + Sync {
    fn apply<PF: PackedField<Scalar = F>>(&self, x_1: PF, x_2: PF) -> (PF, PF);

    #[inline]
    fn apply_in_place<PF: PackedField<Scalar = F>>(&self, x_1: &mut PF, x_2: &mut PF) {
        (*x_1, *x_2) = self.apply(*x_1, *x_2);
    }

    #[inline]
    fn apply_to_rows(&self, row_1: &mut [F], row_2: &mut [F]) {
        let (shorts_1, suffix_1) = F::Packing::pack_slice_with_suffix_mut(row_1);
        let (shorts_2, suffix_2) = F::Packing::pack_slice_with_suffix_mut(row_2);
        debug_assert_eq!(shorts_1.len(), shorts_2.len());
        debug_assert_eq!(suffix_1.len(), suffix_2.len());
        for (x_1, x_2) in shorts_1.iter_mut().zip(shorts_2) {
            self.apply_in_place(x_1, x_2);
        }
        for (x_1, x_2) in suffix_1.iter_mut().zip(suffix_2) {
            self.apply_in_place(x_1, x_2);
        }
    }

    /// Like `apply_to_rows`, but out-of-place.
    #[inline]
    fn apply_to_rows_oop(
        &self,
        src_1: &[F],
        dst_1: &mut [MaybeUninit<F>],
        src_2: &[F],
        dst_2: &mut [MaybeUninit<F>],
    ) {
        let (src_shorts_1, src_suffix_1) = F::Packing::pack_slice_with_suffix(src_1);
        let (src_shorts_2, src_suffix_2) = F::Packing::pack_slice_with_suffix(src_2);
        let (dst_shorts_1, dst_suffix_1) =
            F::Packing::pack_maybe_uninit_slice_with_suffix_mut(dst_1);
        let (dst_shorts_2, dst_suffix_2) =
            F::Packing::pack_maybe_uninit_slice_with_suffix_mut(dst_2);
        debug_assert_eq!(src_shorts_1.len(), src_shorts_2.len());
        debug_assert_eq!(src_suffix_1.len(), src_suffix_2.len());
        debug_assert_eq!(dst_shorts_1.len(), dst_shorts_2.len());
        debug_assert_eq!(dst_suffix_1.len(), dst_suffix_2.len());
        for (s_1, s_2, d_1, d_2) in izip!(src_shorts_1, src_shorts_2, dst_shorts_1, dst_shorts_2) {
            let (res_1, res_2) = self.apply(*s_1, *s_2);
            d_1.write(res_1);
            d_2.write(res_2);
        }
        for (s_1, s_2, d_1, d_2) in izip!(src_suffix_1, src_suffix_2, dst_suffix_1, dst_suffix_2) {
            let (res_1, res_2) = self.apply(*s_1, *s_2);
            d_1.write(res_1);
            d_2.write(res_2);
        }
    }
}

#[derive(Copy, Clone)]
pub struct DifButterfly<F>(pub F);
impl<F: Field> Butterfly<F> for DifButterfly<F> {
    #[inline]
    fn apply<PF: PackedField<Scalar = F>>(&self, x_1: PF, x_2: PF) -> (PF, PF) {
        (x_1 + x_2, (x_1 - x_2) * self.0)
    }
}

#[derive(Copy, Clone)]
pub struct DitButterfly<F>(pub F);
impl<F: Field> Butterfly<F> for DitButterfly<F> {
    #[inline]
    fn apply<PF: PackedField<Scalar = F>>(&self, x_1: PF, x_2: PF) -> (PF, PF) {
        let x_2_twiddle = x_2 * self.0;
        (x_1 + x_2_twiddle, x_1 - x_2_twiddle)
    }
}

/// Butterfly with twiddle factor 1 (works in either DIT or DIF).
#[derive(Copy, Clone)]
pub struct TwiddleFreeButterfly;
impl<F: Field> Butterfly<F> for TwiddleFreeButterfly {
    #[inline]
    fn apply<PF: PackedField<Scalar = F>>(&self, x_1: PF, x_2: PF) -> (PF, PF) {
        (x_1 + x_2, x_1 - x_2)
    }
}
