use core::marker::PhantomData;
use core::time::Duration;
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::BinaryHeap;
use std::collections::LinkedList;
use std::collections::VecDeque;
use std::rc::Rc;
use std::sync::Arc;

#[derive(Default, Eq, PartialEq, Clone, Copy, Debug)]
pub struct AccountId([u8; 32]);

impl From<[u8; 32]> for AccountId {
    fn from(value: [u8; 32]) -> Self {
        Self(value)
    }
}

pub type Balance = u128;

pub trait Encode {}

impl<T> Encode for T {}

pub trait EncodeLike<T: Encode = Self>: Sized + Encode {}

impl<T: ?Sized + Encode> EncodeLike<Box<T>> for Box<T> {}

impl<T: Encode> EncodeLike<T> for Box<T> {}

impl<T: ?Sized + Encode> EncodeLike<&T> for &T {}

impl<T: Encode> EncodeLike<T> for &T {}

impl<T: Encode> EncodeLike<T> for &&T {}

impl<T: ?Sized + Encode> EncodeLike<&mut T> for &mut T {}

impl<T: Encode> EncodeLike<T> for &mut T {}

impl<'a, T: ToOwned + Encode + ?Sized> EncodeLike<Cow<'a, T>> for Cow<'a, T> {}

impl<'a, T: ToOwned + Encode> EncodeLike<T> for Cow<'a, T> {}

impl<T: ?Sized + Encode> EncodeLike<Rc<T>> for Rc<T> {}

impl<T: Encode> EncodeLike<T> for Rc<T> {}

impl EncodeLike<String> for String {}

impl EncodeLike<&str> for String {}

impl EncodeLike<String> for &str {}

impl<T: ?Sized + Encode> EncodeLike<Arc<T>> for Arc<T> {}

impl<T: Encode> EncodeLike<T> for Arc<T> {}

impl<T, LikeT, E, LikeE> EncodeLike<Result<LikeT, LikeE>> for Result<T, E>
where
    T: EncodeLike<LikeT>,
    LikeT: Encode,
    E: EncodeLike<LikeE>,
    LikeE: Encode,
{
}

impl<T: EncodeLike<U>, U: Encode> EncodeLike<Option<U>> for Option<T> {}

impl<T: EncodeLike<U>, U: Encode, const N: usize> EncodeLike<[U; N]> for [T; N] {}

impl<T> EncodeLike<PhantomData<T>> for PhantomData<T> {}

impl<T: EncodeLike<U>, U: Encode> EncodeLike<Vec<U>> for Vec<T> {}

impl<T: EncodeLike<U>, U: Encode> EncodeLike<&[U]> for Vec<T> {}

impl<T: EncodeLike<U>, U: Encode> EncodeLike<Vec<U>> for &[T] {}

impl<K: EncodeLike<LikeK>, LikeK: Encode, V: EncodeLike<LikeV>, LikeV: Encode>
    EncodeLike<BTreeMap<LikeK, LikeV>> for BTreeMap<K, V>
{
}

impl<K: EncodeLike<LikeK>, LikeK: Encode, V: EncodeLike<LikeV>, LikeV: Encode>
    EncodeLike<&[(LikeK, LikeV)]> for BTreeMap<K, V>
{
}

impl<K: EncodeLike<LikeK>, LikeK: Encode, V: EncodeLike<LikeV>, LikeV: Encode>
    EncodeLike<BTreeMap<LikeK, LikeV>> for &[(K, V)]
{
}

impl<T: EncodeLike<LikeT>, LikeT: Encode> EncodeLike<BTreeSet<LikeT>> for BTreeSet<T> {}

impl<T: EncodeLike<LikeT>, LikeT: Encode> EncodeLike<&[(LikeT,)]> for BTreeSet<T> {}

impl<T: EncodeLike<LikeT>, LikeT: Encode> EncodeLike<BTreeSet<LikeT>> for &[(T,)] {}

impl<T: EncodeLike<LikeT>, LikeT: Encode> EncodeLike<LinkedList<LikeT>> for LinkedList<T> {}

impl<T: EncodeLike<LikeT>, LikeT: Encode> EncodeLike<&[(LikeT,)]> for LinkedList<T> {}

impl<T: EncodeLike<LikeT>, LikeT: Encode> EncodeLike<LinkedList<LikeT>> for &[(T,)] {}

impl<T: EncodeLike<LikeT>, LikeT: Encode> EncodeLike<BinaryHeap<LikeT>> for BinaryHeap<T> {}

impl<T: EncodeLike<LikeT>, LikeT: Encode> EncodeLike<&[(LikeT,)]> for BinaryHeap<T> {}

impl<T: EncodeLike<LikeT>, LikeT: Encode> EncodeLike<BinaryHeap<LikeT>> for &[(T,)] {}

impl<T: Encode> EncodeLike<VecDeque<T>> for VecDeque<T> {}

impl<T: EncodeLike<U>, U: Encode> EncodeLike<&[U]> for VecDeque<T> {}

impl<T: EncodeLike<U>, U: Encode> EncodeLike<VecDeque<U>> for &[T] {}

impl<T: EncodeLike<U>, U: Encode> EncodeLike<Vec<U>> for VecDeque<T> {}

impl<T: EncodeLike<U>, U: Encode> EncodeLike<VecDeque<U>> for Vec<T> {}

impl EncodeLike<()> for () {}

impl<
        A0: EncodeLike<A1>,
        A1: Encode,
        B0: EncodeLike<B1>,
        B1: Encode,
        C0: EncodeLike<C1>,
        C1: Encode,
        D0: EncodeLike<D1>,
        D1: Encode,
        E0: EncodeLike<E1>,
        E1: Encode,
        F0: EncodeLike<F1>,
        F1: Encode,
        G0: EncodeLike<G1>,
        G1: Encode,
        H0: EncodeLike<H1>,
        H1: Encode,
        I0: EncodeLike<I1>,
        I1: Encode,
        J0: EncodeLike<J1>,
        J1: Encode,
        K0: EncodeLike<K1>,
        K1: Encode,
        L0: EncodeLike<L1>,
        L1: Encode,
        M0: EncodeLike<M1>,
        M1: Encode,
        N0: EncodeLike<N1>,
        N1: Encode,
        O0: EncodeLike<O1>,
        O1: Encode,
        P0: EncodeLike<P1>,
        P1: Encode,
        Q0: EncodeLike<Q1>,
        Q1: Encode,
        R0: EncodeLike<R1>,
        R1: Encode,
    >
    EncodeLike<(
        A1,
        B1,
        C1,
        D1,
        E1,
        F1,
        G1,
        H1,
        I1,
        J1,
        K1,
        L1,
        M1,
        N1,
        O1,
        P1,
        Q1,
        R1,
    )>
    for (
        A0,
        B0,
        C0,
        D0,
        E0,
        F0,
        G0,
        H0,
        I0,
        J0,
        K0,
        L0,
        M0,
        N0,
        O0,
        P0,
        Q0,
        R0,
    )
{
}

impl<
        B0: EncodeLike<B1>,
        B1: Encode,
        C0: EncodeLike<C1>,
        C1: Encode,
        D0: EncodeLike<D1>,
        D1: Encode,
        E0: EncodeLike<E1>,
        E1: Encode,
        F0: EncodeLike<F1>,
        F1: Encode,
        G0: EncodeLike<G1>,
        G1: Encode,
        H0: EncodeLike<H1>,
        H1: Encode,
        I0: EncodeLike<I1>,
        I1: Encode,
        J0: EncodeLike<J1>,
        J1: Encode,
        K0: EncodeLike<K1>,
        K1: Encode,
        L0: EncodeLike<L1>,
        L1: Encode,
        M0: EncodeLike<M1>,
        M1: Encode,
        N0: EncodeLike<N1>,
        N1: Encode,
        O0: EncodeLike<O1>,
        O1: Encode,
        P0: EncodeLike<P1>,
        P1: Encode,
        Q0: EncodeLike<Q1>,
        Q1: Encode,
        R0: EncodeLike<R1>,
        R1: Encode,
    >
    EncodeLike<(
        B1,
        C1,
        D1,
        E1,
        F1,
        G1,
        H1,
        I1,
        J1,
        K1,
        L1,
        M1,
        N1,
        O1,
        P1,
        Q1,
        R1,
    )>
    for (
        B0,
        C0,
        D0,
        E0,
        F0,
        G0,
        H0,
        I0,
        J0,
        K0,
        L0,
        M0,
        N0,
        O0,
        P0,
        Q0,
        R0,
    )
{
}

impl<
        C0: EncodeLike<C1>,
        C1: Encode,
        D0: EncodeLike<D1>,
        D1: Encode,
        E0: EncodeLike<E1>,
        E1: Encode,
        F0: EncodeLike<F1>,
        F1: Encode,
        G0: EncodeLike<G1>,
        G1: Encode,
        H0: EncodeLike<H1>,
        H1: Encode,
        I0: EncodeLike<I1>,
        I1: Encode,
        J0: EncodeLike<J1>,
        J1: Encode,
        K0: EncodeLike<K1>,
        K1: Encode,
        L0: EncodeLike<L1>,
        L1: Encode,
        M0: EncodeLike<M1>,
        M1: Encode,
        N0: EncodeLike<N1>,
        N1: Encode,
        O0: EncodeLike<O1>,
        O1: Encode,
        P0: EncodeLike<P1>,
        P1: Encode,
        Q0: EncodeLike<Q1>,
        Q1: Encode,
        R0: EncodeLike<R1>,
        R1: Encode,
    >
    EncodeLike<(
        C1,
        D1,
        E1,
        F1,
        G1,
        H1,
        I1,
        J1,
        K1,
        L1,
        M1,
        N1,
        O1,
        P1,
        Q1,
        R1,
    )>
    for (
        C0,
        D0,
        E0,
        F0,
        G0,
        H0,
        I0,
        J0,
        K0,
        L0,
        M0,
        N0,
        O0,
        P0,
        Q0,
        R0,
    )
{
}

impl<
        D0: EncodeLike<D1>,
        D1: Encode,
        E0: EncodeLike<E1>,
        E1: Encode,
        F0: EncodeLike<F1>,
        F1: Encode,
        G0: EncodeLike<G1>,
        G1: Encode,
        H0: EncodeLike<H1>,
        H1: Encode,
        I0: EncodeLike<I1>,
        I1: Encode,
        J0: EncodeLike<J1>,
        J1: Encode,
        K0: EncodeLike<K1>,
        K1: Encode,
        L0: EncodeLike<L1>,
        L1: Encode,
        M0: EncodeLike<M1>,
        M1: Encode,
        N0: EncodeLike<N1>,
        N1: Encode,
        O0: EncodeLike<O1>,
        O1: Encode,
        P0: EncodeLike<P1>,
        P1: Encode,
        Q0: EncodeLike<Q1>,
        Q1: Encode,
        R0: EncodeLike<R1>,
        R1: Encode,
    > EncodeLike<(D1, E1, F1, G1, H1, I1, J1, K1, L1, M1, N1, O1, P1, Q1, R1)>
    for (D0, E0, F0, G0, H0, I0, J0, K0, L0, M0, N0, O0, P0, Q0, R0)
{
}

impl<
        E0: EncodeLike<E1>,
        E1: Encode,
        F0: EncodeLike<F1>,
        F1: Encode,
        G0: EncodeLike<G1>,
        G1: Encode,
        H0: EncodeLike<H1>,
        H1: Encode,
        I0: EncodeLike<I1>,
        I1: Encode,
        J0: EncodeLike<J1>,
        J1: Encode,
        K0: EncodeLike<K1>,
        K1: Encode,
        L0: EncodeLike<L1>,
        L1: Encode,
        M0: EncodeLike<M1>,
        M1: Encode,
        N0: EncodeLike<N1>,
        N1: Encode,
        O0: EncodeLike<O1>,
        O1: Encode,
        P0: EncodeLike<P1>,
        P1: Encode,
        Q0: EncodeLike<Q1>,
        Q1: Encode,
        R0: EncodeLike<R1>,
        R1: Encode,
    > EncodeLike<(E1, F1, G1, H1, I1, J1, K1, L1, M1, N1, O1, P1, Q1, R1)>
    for (E0, F0, G0, H0, I0, J0, K0, L0, M0, N0, O0, P0, Q0, R0)
{
}

impl<
        F0: EncodeLike<F1>,
        F1: Encode,
        G0: EncodeLike<G1>,
        G1: Encode,
        H0: EncodeLike<H1>,
        H1: Encode,
        I0: EncodeLike<I1>,
        I1: Encode,
        J0: EncodeLike<J1>,
        J1: Encode,
        K0: EncodeLike<K1>,
        K1: Encode,
        L0: EncodeLike<L1>,
        L1: Encode,
        M0: EncodeLike<M1>,
        M1: Encode,
        N0: EncodeLike<N1>,
        N1: Encode,
        O0: EncodeLike<O1>,
        O1: Encode,
        P0: EncodeLike<P1>,
        P1: Encode,
        Q0: EncodeLike<Q1>,
        Q1: Encode,
        R0: EncodeLike<R1>,
        R1: Encode,
    > EncodeLike<(F1, G1, H1, I1, J1, K1, L1, M1, N1, O1, P1, Q1, R1)>
    for (F0, G0, H0, I0, J0, K0, L0, M0, N0, O0, P0, Q0, R0)
{
}

impl<
        G0: EncodeLike<G1>,
        G1: Encode,
        H0: EncodeLike<H1>,
        H1: Encode,
        I0: EncodeLike<I1>,
        I1: Encode,
        J0: EncodeLike<J1>,
        J1: Encode,
        K0: EncodeLike<K1>,
        K1: Encode,
        L0: EncodeLike<L1>,
        L1: Encode,
        M0: EncodeLike<M1>,
        M1: Encode,
        N0: EncodeLike<N1>,
        N1: Encode,
        O0: EncodeLike<O1>,
        O1: Encode,
        P0: EncodeLike<P1>,
        P1: Encode,
        Q0: EncodeLike<Q1>,
        Q1: Encode,
        R0: EncodeLike<R1>,
        R1: Encode,
    > EncodeLike<(G1, H1, I1, J1, K1, L1, M1, N1, O1, P1, Q1, R1)>
    for (G0, H0, I0, J0, K0, L0, M0, N0, O0, P0, Q0, R0)
{
}

impl<
        H0: EncodeLike<H1>,
        H1: Encode,
        I0: EncodeLike<I1>,
        I1: Encode,
        J0: EncodeLike<J1>,
        J1: Encode,
        K0: EncodeLike<K1>,
        K1: Encode,
        L0: EncodeLike<L1>,
        L1: Encode,
        M0: EncodeLike<M1>,
        M1: Encode,
        N0: EncodeLike<N1>,
        N1: Encode,
        O0: EncodeLike<O1>,
        O1: Encode,
        P0: EncodeLike<P1>,
        P1: Encode,
        Q0: EncodeLike<Q1>,
        Q1: Encode,
        R0: EncodeLike<R1>,
        R1: Encode,
    > EncodeLike<(H1, I1, J1, K1, L1, M1, N1, O1, P1, Q1, R1)>
    for (H0, I0, J0, K0, L0, M0, N0, O0, P0, Q0, R0)
{
}

impl<
        I0: EncodeLike<I1>,
        I1: Encode,
        J0: EncodeLike<J1>,
        J1: Encode,
        K0: EncodeLike<K1>,
        K1: Encode,
        L0: EncodeLike<L1>,
        L1: Encode,
        M0: EncodeLike<M1>,
        M1: Encode,
        N0: EncodeLike<N1>,
        N1: Encode,
        O0: EncodeLike<O1>,
        O1: Encode,
        P0: EncodeLike<P1>,
        P1: Encode,
        Q0: EncodeLike<Q1>,
        Q1: Encode,
        R0: EncodeLike<R1>,
        R1: Encode,
    > EncodeLike<(I1, J1, K1, L1, M1, N1, O1, P1, Q1, R1)>
    for (I0, J0, K0, L0, M0, N0, O0, P0, Q0, R0)
{
}

impl<
        J0: EncodeLike<J1>,
        J1: Encode,
        K0: EncodeLike<K1>,
        K1: Encode,
        L0: EncodeLike<L1>,
        L1: Encode,
        M0: EncodeLike<M1>,
        M1: Encode,
        N0: EncodeLike<N1>,
        N1: Encode,
        O0: EncodeLike<O1>,
        O1: Encode,
        P0: EncodeLike<P1>,
        P1: Encode,
        Q0: EncodeLike<Q1>,
        Q1: Encode,
        R0: EncodeLike<R1>,
        R1: Encode,
    > EncodeLike<(J1, K1, L1, M1, N1, O1, P1, Q1, R1)> for (J0, K0, L0, M0, N0, O0, P0, Q0, R0)
{
}

impl<
        K0: EncodeLike<K1>,
        K1: Encode,
        L0: EncodeLike<L1>,
        L1: Encode,
        M0: EncodeLike<M1>,
        M1: Encode,
        N0: EncodeLike<N1>,
        N1: Encode,
        O0: EncodeLike<O1>,
        O1: Encode,
        P0: EncodeLike<P1>,
        P1: Encode,
        Q0: EncodeLike<Q1>,
        Q1: Encode,
        R0: EncodeLike<R1>,
        R1: Encode,
    > EncodeLike<(K1, L1, M1, N1, O1, P1, Q1, R1)> for (K0, L0, M0, N0, O0, P0, Q0, R0)
{
}

impl<
        L0: EncodeLike<L1>,
        L1: Encode,
        M0: EncodeLike<M1>,
        M1: Encode,
        N0: EncodeLike<N1>,
        N1: Encode,
        O0: EncodeLike<O1>,
        O1: Encode,
        P0: EncodeLike<P1>,
        P1: Encode,
        Q0: EncodeLike<Q1>,
        Q1: Encode,
        R0: EncodeLike<R1>,
        R1: Encode,
    > EncodeLike<(L1, M1, N1, O1, P1, Q1, R1)> for (L0, M0, N0, O0, P0, Q0, R0)
{
}

impl<
        M0: EncodeLike<M1>,
        M1: Encode,
        N0: EncodeLike<N1>,
        N1: Encode,
        O0: EncodeLike<O1>,
        O1: Encode,
        P0: EncodeLike<P1>,
        P1: Encode,
        Q0: EncodeLike<Q1>,
        Q1: Encode,
        R0: EncodeLike<R1>,
        R1: Encode,
    > EncodeLike<(M1, N1, O1, P1, Q1, R1)> for (M0, N0, O0, P0, Q0, R0)
{
}

impl<
        N0: EncodeLike<N1>,
        N1: Encode,
        O0: EncodeLike<O1>,
        O1: Encode,
        P0: EncodeLike<P1>,
        P1: Encode,
        Q0: EncodeLike<Q1>,
        Q1: Encode,
        R0: EncodeLike<R1>,
        R1: Encode,
    > EncodeLike<(N1, O1, P1, Q1, R1)> for (N0, O0, P0, Q0, R0)
{
}

impl<
        O0: EncodeLike<O1>,
        O1: Encode,
        P0: EncodeLike<P1>,
        P1: Encode,
        Q0: EncodeLike<Q1>,
        Q1: Encode,
        R0: EncodeLike<R1>,
        R1: Encode,
    > EncodeLike<(O1, P1, Q1, R1)> for (O0, P0, Q0, R0)
{
}

impl<
        P0: EncodeLike<P1>,
        P1: Encode,
        Q0: EncodeLike<Q1>,
        Q1: Encode,
        R0: EncodeLike<R1>,
        R1: Encode,
    > EncodeLike<(P1, Q1, R1)> for (P0, Q0, R0)
{
}

impl<Q0: EncodeLike<Q1>, Q1: Encode, R0: EncodeLike<R1>, R1: Encode> EncodeLike<(Q1, R1)>
    for (Q0, R0)
{
}

impl<R0: EncodeLike<R1>, R1: Encode> EncodeLike<(R1,)> for (R0,) {}

impl EncodeLike<u16> for u16 {}

impl EncodeLike<u32> for u32 {}

impl EncodeLike<u64> for u64 {}

impl EncodeLike<u128> for u128 {}

impl EncodeLike<i16> for i16 {}

impl EncodeLike<i32> for i32 {}

impl EncodeLike<i64> for i64 {}

impl EncodeLike<i128> for i128 {}

impl EncodeLike<u8> for u8 {}

impl EncodeLike<i8> for i8 {}

impl EncodeLike<f32> for f32 {}

impl EncodeLike<f64> for f64 {}

impl EncodeLike<bool> for bool {}

impl EncodeLike<Duration> for Duration {}

impl EncodeLike<AccountId> for AccountId {}

#[derive(Default)]
pub struct Mapping<K: 'static, V: 'static>(&'static [(K, V)]);

impl<K, V> Mapping<K, V> {
    pub fn insert<Q: EncodeLike<K>, R: EncodeLike<V>>(&mut self, key: Q, value: &R) {
        unimplemented!()
    }

    pub fn get<Q: EncodeLike<K>>(&self, key: Q) -> Option<V> {
        unimplemented!()
    }

    pub fn contains<Q: EncodeLike<K>>(&self, key: Q) -> bool {
        unimplemented!()
    }

    pub fn remove<Q: EncodeLike<K>>(&self, key: Q) {
        unimplemented!()
    }
}

pub struct Env;

impl Env {
    pub fn caller(&self) -> AccountId {
        unimplemented!()
    }

    pub fn emit_event<A>(&self, event: A) {}
}

#[macro_export]
macro_rules! impl_storage {
    ($struct_name:ident) => {
        impl $struct_name {
            fn init_env() -> Env {
                unimplemented!()
            }

            fn env(&self) -> Env {
                unimplemented!()
            }
        }
    };
}

// scale::Encode
impl std::fmt::Debug for dyn Encode {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
      write!(f, "{}", "Encode")
  }
}

pub trait Decode {}

// scale::Decode
impl std::fmt::Debug for dyn Decode {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
      write!(f, "{}", "Decode")
  }
}

// ink::prelude::string
pub mod string {
  pub struct String {}
}

// ink::env::vec
pub mod vec {
  pub struct Vec<T> {}
}

pub struct Args {}
pub struct Call<E: Environment> {
  // dest : MultiAddress<E::AccountId, ()>,
  // value : E::Balance,
  // gas_limit : Weight,
  // storage_deposit_limit : Option<E::Balance>,
  // data : Vec<u8>,
}

pub struct EmptyArgumentList {}
pub struct ReturnType<T>(marker::PhantomData<fn() -> T>);
pub struct Unset<T>(marker::PhantomData<fn() -> T>);

// ink::env::call
pub mod call {
  // pub fn build_call<E>() -> CallBuilder<
  //     E,
  //     Unset<Call<E>>,
  //     Unset<ExecutionInput<EmptyArgumentList>>,
  //     Unset<ReturnType<()>>,
  // >
  // where
  //     E: Environment,
  // {
  //     CallBuilder {
  //         call_type: Default::default(),
  //         call_flags: Default::default(),
  //         exec_input: Default::default(),
  //         return_type: Default::default(),
  //         _phantom: Default::default(),
  //     }
  // }
  use crate::storage::Environment;
  pub fn build_call<E>() -> CallBuilder<
    E,
    Unset<Call<E>>,
    Unset<ExecutionInput<EmptyArgumentList>>,
    Unset<ReturnType<()>>,
  >
  where
    E: Environment
  { unimplemented!() }

  pub struct Selector {
    bytes: [u8; 4],
  }
  pub struct ExecutionInput<Args> {
    selector: Selector,
    args: Args,
  }


}

// ink::env::DefaultEnvironment
pub enum DefaultEnvironment {}

// ink::env::Environment
pub trait Environment {
  type AccountId;
  type Balance;
  type Hash;
  type Timestamp;
  type BlockNumber;
  type ChainExtension;

  const MAX_EVENT_TOPICS: usize;
}

pub struct OffChainError {}

pub struct ScaleError {} // parity_scale_codec::Error

// ink::env::Error
pub enum Error {
  Decode(ScaleError),
  OffChain(OffChainError),
  CalleeTrapped,
  CalleeReverted,
  KeyNotFound,
  _BelowSubsistenceThreshold,
  TransferFailed,
  _EndowmentTooLow,
  CodeNotFound,
  NotCallable,
  Unknown,
  LoggingDisabled,
  CallRuntimeFailed,
  EcdsaRecoveryFailed,
}

// ink::env::debug_println
#[macro_export]
macro_rules! debug_println {
  () => { unimplemented!() };
  ($($arg:tt)*) => { unimplemented!() };
}