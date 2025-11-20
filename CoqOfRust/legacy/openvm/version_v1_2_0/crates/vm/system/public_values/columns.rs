use std::marker::PhantomData;

pub(crate) struct PublicValuesCoreColsView<'a, T, R> {
    pub is_valid: R,
    /// The value to publish.
    pub value: R,
    /// The index of the public value to publish.
    pub index: R,
    pub custom_pv_vars: Vec<R>,
    pub(crate) _marker: PhantomData<&'a T>,
}

impl<T, R> PublicValuesCoreColsView<'_, T, R> {
    pub(crate) fn width(&self) -> usize {
        3 + self.custom_pv_vars.len()
    }
    #[allow(dead_code)]
    pub(crate) fn flatten(self) -> Vec<R> {
        [self.is_valid, self.value, self.index]
            .into_iter()
            .chain(self.custom_pv_vars)
            .collect()
    }
}
impl<'a, T> PublicValuesCoreColsView<'a, T, &'a T> {
    pub(crate) fn borrow(arr: &'a [T]) -> PublicValuesCoreColsView<'a, T, &'a T> {
        PublicValuesCoreColsView::<T, &'a T> {
            is_valid: &arr[0],
            value: &arr[1],
            index: &arr[2],
            custom_pv_vars: arr[3..].iter().collect(),
            _marker: Default::default(),
        }
    }
}
impl<'a, T> PublicValuesCoreColsView<'a, T, &'a mut T> {
    pub(crate) fn borrow_mut(arr: &'a mut [T]) -> PublicValuesCoreColsView<'a, T, &'a mut T> {
        let (first_three, rest) = arr.split_at_mut(3);
        let [is_valid, value, index] = first_three else {
            unreachable!("first_three should have exactly 3 elements");
        };
        PublicValuesCoreColsView::<T, &'a mut T> {
            is_valid,
            value,
            index,
            custom_pv_vars: rest.iter_mut().collect(),
            _marker: Default::default(),
        }
    }
}
