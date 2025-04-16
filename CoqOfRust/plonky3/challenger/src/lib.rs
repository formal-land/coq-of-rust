//! Utilities for generating Fiat-Shamir challenges based on an IOP's transcript.

#![no_std]

extern crate alloc;

mod duplex_challenger;
mod grinding_challenger;
mod hash_challenger;
mod multi_field_challenger;
mod serializing_challenger;

use alloc::vec::Vec;
use core::array;

pub use duplex_challenger::*;
pub use grinding_challenger::*;
pub use hash_challenger::*;
pub use multi_field_challenger::*;
use p3_field::{BasedVectorSpace, Field};
pub use serializing_challenger::*;

pub trait CanObserve<T> {
    fn observe(&mut self, value: T);

    fn observe_slice(&mut self, values: &[T])
    where
        T: Clone,
    {
        for value in values {
            self.observe(value.clone());
        }
    }
}

pub trait CanSample<T> {
    fn sample(&mut self) -> T;

    fn sample_array<const N: usize>(&mut self) -> [T; N] {
        array::from_fn(|_| self.sample())
    }

    fn sample_vec(&mut self, n: usize) -> Vec<T> {
        (0..n).map(|_| self.sample()).collect()
    }
}

pub trait CanSampleBits<T> {
    fn sample_bits(&mut self, bits: usize) -> T;
}

pub trait FieldChallenger<F: Field>:
    CanObserve<F> + CanSample<F> + CanSampleBits<usize> + Sync
{
    fn observe_algebra_element<A: BasedVectorSpace<F>>(&mut self, alg_elem: A) {
        self.observe_slice(alg_elem.as_basis_coefficients_slice());
    }

    fn sample_algebra_element<A: BasedVectorSpace<F>>(&mut self) -> A {
        A::from_basis_coefficients_fn(|_| self.sample())
    }
}

impl<C, T> CanObserve<T> for &mut C
where
    C: CanObserve<T>,
{
    #[inline(always)]
    fn observe(&mut self, value: T) {
        (*self).observe(value)
    }

    #[inline(always)]
    fn observe_slice(&mut self, values: &[T])
    where
        T: Clone,
    {
        (*self).observe_slice(values)
    }
}

impl<C, T> CanSample<T> for &mut C
where
    C: CanSample<T>,
{
    #[inline(always)]
    fn sample(&mut self) -> T {
        (*self).sample()
    }

    #[inline(always)]
    fn sample_array<const N: usize>(&mut self) -> [T; N] {
        (*self).sample_array()
    }

    #[inline(always)]
    fn sample_vec(&mut self, n: usize) -> Vec<T> {
        (*self).sample_vec(n)
    }
}

impl<C, T> CanSampleBits<T> for &mut C
where
    C: CanSampleBits<T>,
{
    #[inline(always)]
    fn sample_bits(&mut self, bits: usize) -> T {
        (*self).sample_bits(bits)
    }
}

impl<C, F: Field> FieldChallenger<F> for &mut C
where
    C: FieldChallenger<F>,
{
    #[inline(always)]
    fn observe_algebra_element<EF: BasedVectorSpace<F>>(&mut self, ext: EF) {
        (*self).observe_algebra_element(ext)
    }

    #[inline(always)]
    fn sample_algebra_element<EF: BasedVectorSpace<F>>(&mut self) -> EF {
        (*self).sample_algebra_element()
    }
}
