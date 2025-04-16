pub trait CryptographicHasher<Item: Clone, Out>: Clone {
    fn hash_iter<I>(&self, input: I) -> Out
    where
        I: IntoIterator<Item = Item>;

    fn hash_iter_slices<'a, I>(&self, input: I) -> Out
    where
        I: IntoIterator<Item = &'a [Item]>,
        Item: 'a,
    {
        self.hash_iter(input.into_iter().flatten().cloned())
    }

    fn hash_slice(&self, input: &[Item]) -> Out {
        self.hash_iter_slices(core::iter::once(input))
    }

    fn hash_item(&self, input: Item) -> Out {
        self.hash_slice(&[input])
    }
}
