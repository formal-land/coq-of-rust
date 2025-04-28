/// An iterator which iterates two other iterators of the same length simultaneously.
///
/// Equality of the lengths of `a` abd `b` are at construction time.
#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
pub struct ZipEq<A, B> {
    a: A,
    b: B,
}

/// Zips two iterators but **panics** if they are not of the same length.
///
/// Similar to `itertools::zip_eq`, but we check the lengths at construction time.
pub fn zip_eq<A, AIter, B, BIter, Error>(
    a: A,
    b: B,
    err: Error,
) -> Result<ZipEq<A::IntoIter, B::IntoIter>, Error>
where
    A: IntoIterator<IntoIter = AIter>,
    AIter: ExactSizeIterator,
    B: IntoIterator<IntoIter = BIter>,
    BIter: ExactSizeIterator,
{
    let a_iter = a.into_iter();
    let b_iter = b.into_iter();
    match a_iter.len() == b_iter.len() {
        true => Ok(ZipEq {
            a: a_iter,
            b: b_iter,
        }),
        false => Err(err),
    }
}

impl<A, B> Iterator for ZipEq<A, B>
where
    A: ExactSizeIterator, // We need to use ExactSizeIterator here otherwise the size_hint() methods could differ.
    B: ExactSizeIterator,
{
    type Item = (A::Item, B::Item);

    fn next(&mut self) -> Option<Self::Item> {
        match (self.a.next(), self.b.next()) {
            (Some(a), Some(b)) => Some((a, b)),
            (None, None) => None,
            _ => unreachable!("The iterators must have the same length."),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // self.a.size_hint() = self.b.size_hint() as a and b are ExactSizeIterators
        // and we checked that they are the same length at construction time.
        debug_assert_eq!(self.a.size_hint(), self.b.size_hint());
        self.a.size_hint()
    }
}

impl<A, B> ExactSizeIterator for ZipEq<A, B>
where
    A: ExactSizeIterator,
    B: ExactSizeIterator,
{
}
