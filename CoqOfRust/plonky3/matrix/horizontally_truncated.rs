use core::iter::Take;
use core::marker::PhantomData;

use crate::Matrix;

pub struct HorizontallyTruncated<T, Inner> {
    inner: Inner,
    truncated_width: usize,
    _phantom: PhantomData<T>,
}

impl<T, Inner: Matrix<T>> HorizontallyTruncated<T, Inner>
where
    T: Send + Sync,
{
    pub fn new(inner: Inner, truncated_width: usize) -> Self {
        assert!(truncated_width <= inner.width());
        Self {
            inner,
            truncated_width,
            _phantom: PhantomData,
        }
    }
}

impl<T, Inner> Matrix<T> for HorizontallyTruncated<T, Inner>
where
    T: Send + Sync,
    Inner: Matrix<T>,
{
    #[inline(always)]
    fn width(&self) -> usize {
        self.truncated_width
    }

    #[inline(always)]
    fn height(&self) -> usize {
        self.inner.height()
    }

    #[inline(always)]
    fn get(&self, r: usize, c: usize) -> T {
        debug_assert!(c < self.truncated_width);
        self.inner.get(c, r)
    }

    type Row<'a>
        = Take<Inner::Row<'a>>
    where
        Self: 'a;

    #[inline(always)]
    fn row(&self, r: usize) -> Self::Row<'_> {
        self.inner.row(r).take(self.truncated_width)
    }
}
