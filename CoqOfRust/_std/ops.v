Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust._std.pin.
Require Import CoqOfRust.core.cmp.
Require Import CoqOfRust.core.marker.


(* ********ENUMS******** *)
(* 
[x] GeneratorState
[x] Bound
[x] ControlFlow
*)

(* 
pub enum GeneratorState<Y, R> {
    Yielded(Y),
    Complete(R),
}
*)
Module GeneratorState.
  Inductive t (Y R : Set) : Set := 
  | Yielded : Y -> t Y R
  | Complete : Y -> t Y R
  .
End GeneratorState.
Definition GeneratorState := GeneratorState.t.

(* 
pub enum Bound<T> {
    Included(T),
    Excluded(T),
    Unbounded,
}
*)
Module Bound.
  Inductive t (T : Set) : Set := 
  | Included : T -> t T
  | Excluded : T -> t T
  | Unbounded : t T
  .
End Bound.
Definition Bound := Bound.t.

(* 
pub enum ControlFlow<B, C = ()> {
    Continue(C),
    Break(B),
}
*)
Module ControlFlow.
  Inductive t (B C : Set) : Set := 
  | Continue : C -> t B C
  | Break : B -> t B C
  .
End ControlFlow.
Definition ControlFlow (B : Set) (C : Set) : Set :=
  M.Val (ControlFlow.t B C).

(* ********STRUCTS******** *)
(* 
[x] Yeet
[x] Range
[x] RangeFrom
[x] RangeFull
[x] RangeInclusive
[x] RangeTo
[x] RangeToInclusive
*)

(* pub struct Yeet<T>(pub T); *)
Module Yeet.
  Record t (T : Set) : Set := { _1 : T }.
End Yeet.
Definition Yeet := Yeet.t.

(* 
pub struct Range<Idx> {
    pub start: Idx,
    pub end: Idx,
}
*)
Module Range.
  Record t (Idx : Set) : Set := { 
    start : Idx;
    _end : Idx;
  }.
End Range.
Definition Range := Range.t.

(* 
pub struct RangeFrom<Idx> {
    pub start: Idx,
}
*)
Module RangeFrom.
  Record t (Idx : Set) : Set := { 
    start : Idx;
  }.
End RangeFrom.
Definition RangeFrom := RangeFrom.t.

(* pub struct RangeFull; *)
Module RangeFull.
  Inductive t : Set := Build.
End RangeFull.
Definition RangeFull := RangeFull.t.

(* pub struct RangeInclusive<Idx> { /* private fields */ } *)
Module RangeInclusive.
  Parameter t : forall (Idx : Set), Set.
End RangeInclusive.
Definition RangeInclusive := RangeInclusive.t.

(* 
pub struct RangeTo<Idx> {
    pub end: Idx,
}
*)
Module RangeTo.
  Record t (Idx : Set) : Set := { 
    _end : Idx;
  }.
End RangeTo.
Definition RangeTo := RangeTo.t.

(* 
pub struct RangeToInclusive<Idx> {
    pub end: Idx,
}
*)
Module RangeToInclusive.
  Record t (Idx : Set) : Set := { 
    _end : Idx;
  }.
End RangeToInclusive.
Definition RangeToInclusive := RangeToInclusive.t.

(* ********TRAITS******** *)
(* 
[x] CoerceUnsized
[x] DispatchFromDyn
[ ] FromResidual
[x] Generator
[x] OneSidedRange
[ ] Residual
[ ] Try
[x] Add
[x] AddAssign
[x] BitAnd
[x] BitAndAssign
[x] BitOr
[x] BitOrAssign
[x] BitXor
[x] BitXorAssign
[x] Deref
[x] DerefMut
[x] Div
[x] DivAssign
[x] Drop
[x] Fn
[x] FnMut
[x] FnOnce
[x] Index
[x] IndexMut
[x] Mul	
[x] MulAssign
[x] Neg
[x] Not
[x] RangeBounds
[x] Rem
[x] RemAssign
[x] Shl
[x] ShlAssign
[x] Shr
[x] ShrAssign
[x] Sub
[x] SubAssign
*)

(* 
pub trait CoerceUnsized<T>
where
    T: ?Sized,
{ }
*)
Module CoerseUnsized.
  Unset Primitive Projections.
  Class Trait (Self : Set) (T : Set) : Set := { }.
  Set Primitive Projections.
End CoerseUnsized.

(* pub trait DispatchFromDyn<T> { } *)
Module DispatchFromDyn.
  Unset Primitive Projections.
  Class Trait (Self : Set) (T : Set) : Set := { }.
  Set Primitive Projections.
End DispatchFromDyn.

(* BUGGED: Mutual reference of FromResidual and Try *)
(* 
pub trait Try: FromResidual<Self::Residual> {
    type Output;
    type Residual;

    // Required methods
    fn from_output(output: Self::Output) -> Self;
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output>;
}
*)
Module Try.
  Unset Primitive Projections.
  Class Trait (Self : Set) : Set := { }.
  Set Primitive Projections.
End Try.

(* BUGGED: Same as above *)
(* 
pub trait FromResidual<R = <Self as Try>::Residual> {
    // Required method
    fn from_residual(residual: R) -> Self;
}
*)
Module FromResidual.
  Unset Primitive Projections.
  Class Trait (Self : Set) : Set := { }.
  Set Primitive Projections.
End FromResidual.

(* 
pub trait Generator<R = ()> {
    type Yield;
    type Return;

    // Required method
    fn resume(
        self: Pin<&mut Self>,
        arg: R
    ) -> GeneratorState<Self::Yield, Self::Return>;
}
*)
Module Generator.
  Class Trait (Self : Set) (R : option Set) (Yield Return : Set) : Set := {
    R := defaultType R unit;
    Yield := Yield;
    Return := Return;
    resume : Pin (mut_ref Self) -> R -> GeneratorState Yield Return;
  }.
End Generator.

(* 
pub trait RangeBounds<T>
where
    T: ?Sized,
{
    // Required methods
    fn start_bound(&self) -> Bound<&T>;
    fn end_bound(&self) -> Bound<&T>;

    // Provided method
    fn contains<U>(&self, item: &U) -> bool
       where T: PartialOrd<U>,
             U: PartialOrd<T> + ?Sized { ... }
}
*)
Module RangeBounds.
  Class Trait (Self T : Set) : Set := { 
    start_bound : ref Self -> Bound (ref T);
    end_bound : ref Self -> Bound (ref T);
    contains (U : Set) {T : Set}
      `{PartialOrd.Trait U (Rhs := T)}
      `{PartialOrd.Trait T (Rhs := U)}
      : ref Self -> ref U -> bool;
  }.
End RangeBounds.


(* 
pub trait OneSidedRange<T>: RangeBounds<T>
where
    T: ?Sized,
{ }
*)
Module OneSidedRange.
  Unset Primitive Projections.
  Class Trait (Self : Set) (T : Set)
    `{RangeBounds.Trait Self T}
  : Set := { }.
  Set Primitive Projections.
End OneSidedRange.

(* 
pub trait FnOnce<Args>
where
    Args: Tuple,
{
    type Output;

    // Required method
    extern "rust-call" fn call_once(self, args: Args) -> Self::Output;
}
*)
Module FnOnce.
  Class Trait (Self : Set) (Args Output : Set) 
  `{Tuple.Trait Args}
  : Set := { 
    call_once : Self -> Args -> Output;
  }.
End FnOnce.

(* NOTE: Is this the reason that the Output can be implicit? *)
(* NOTE: Beware of the arguments for traits, in particular orders and the corresponded params *)
(* 
pub trait FnMut<Args>: FnOnce<Args>
where
    Args: Tuple,
{
    // Required method
    extern "rust-call" fn call_mut(
        &mut self,
        args: Args
    ) -> Self::Output;
}
*)
Module FnMut.
  Class Trait (Self : Set) (Args Output : Set) 
    `{FnOnce.Trait Self Args}
    (* Note: can we just write `Args : Tuple`? *)
    `{Tuple.Trait Args}
  : Set := { 
    call_mut : mut_ref Self -> Args -> Output;
  }.
End FnMut.


(* 
pub trait Fn<Args>: FnMut<Args>
where
    Args: Tuple,
{
    // Required method
    extern "rust-call" fn call(&self, args: Args) -> Self::Output;
}
*)
Module Fn.
  Class Trait (Self : Set) (Args : Set) (Output : Set)
    `{Tuple.Trait Args}
    `{FnMut.Trait Self Args}
  : Set := { 
    call : ref Self -> Args -> Output;
  }.
End Fn.

(* 
pub trait Index<Idx>
where
    Idx: ?Sized,
{
    type Output: ?Sized;

    // Required method
    fn index(&self, index: Idx) -> &Self::Output;
}
*)
Module Index.
  Class Trait (Self : Set) (Idx : Set) (Output : Set) : Set := {
    index : ref Self -> Idx -> Output;
  }.
End Index.

(* 
pub trait IndexMut<Idx>: Index<Idx>
where
    Idx: ?Sized,
{
    // Required method
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output;
}
*)
Module IndexMut.
  Class Trait (Self : Set) (Idx : Set) 
    `{Index.Trait Self Idx}
  : Set := { 
    index_mut : mut_ref Self -> Idx -> Output;
  }.
End IndexMut.
