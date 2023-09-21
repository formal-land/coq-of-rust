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
Definition ControlFlow (B : Set) (C : option Set) := 
  ControlFlow.t B (defaultType C unit).

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
    _end : Idx
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

(* Binary Operators *)
Module Add.
  Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
    Output := Output;
    Rhs := defaultType Rhs Self;
    add : Self -> Rhs -> Output;
  }.

  Global Instance Method_add `(Trait) : Notation.Dot "add" := {
    Notation.dot := add;
  }.
End Add.

Module AddAssign.
  Class Trait (Self : Set) (Rhs : option Set) : Set := {
    Rhs := defaultType Rhs Self;
    add_assign : mut_ref Self -> Rhs -> unit;
  }.

  Global Instance Method_add_assign `(Trait) : Notation.Dot "add_assign" := {
    Notation.dot := add_assign;
  }.
End AddAssign.

Module Sub.
  Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
    Output := Output;
    Rhs := defaultType Rhs Self;
    sub : Self -> Rhs -> Output;
  }.

  Global Instance Method_sub `(Trait) : Notation.Dot "sub" := {
    Notation.dot := sub;
  }.
End Sub.

Module SubAssign.
  Class Trait (Self : Set) (Rhs : option Set) : Set := {
    Rhs := defaultType Rhs Self;
    sub_assign : mut_ref Self -> Rhs -> unit;
  }.

  Global Instance Method_sub_assign `(Trait) : Notation.Dot "sub_assign" := {
    Notation.dot := sub_assign;
  }.
End SubAssign.

Module Mul.
  Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
    Output := Output;
    Rhs := defaultType Rhs Self;
    mul : Self -> Rhs -> Output;
  }.

  Global Instance Method_mul `(Trait) : Notation.Dot "mul" := {
    Notation.dot := mul;
  }.
End Mul.

Module MulAssign.
  Class Trait (Self : Set) (Rhs : option Set) : Set := {
    Rhs := defaultType Rhs Self;
    mul_assign : mut_ref Self -> Rhs -> unit;
  }.

  Global Instance Method_mul_assign `(Trait) : Notation.Dot "mul_assign" := {
    Notation.dot := mul_assign;
  }.
End MulAssign.

Module Div.
  Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
    Output := Output;
    Rhs := defaultType Rhs Self;
    div : Self -> Rhs -> Output;
  }.

  Global Instance Method_div `(Trait) : Notation.Dot "div" := {
    Notation.dot := div;
  }.
End Div.

Module DivAssign.
  Class Trait (Self : Set) (Rhs : option Set) : Set := {
    Rhs := defaultType Rhs Self;
    div_assign : mut_ref Self -> Rhs -> unit;
  }.

  Global Instance Method_div_assign `(Trait) : Notation.Dot "div_assign" := {
    Notation.dot := div_assign;
  }.
End DivAssign.

(* 
pub trait Drop {
    // Required method
    fn drop(&mut self);
}
*)
Module Drop.
  Class Trait (Self : Set) : Set := {
    drop : mut_ref Self;
  }.
End Drop.

Module Rem.
  Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
    Output := Output;
    Rhs := defaultType Rhs Self;
    rem : Self -> Rhs -> Output;
  }.

  Global Instance Method_rem `(Trait) : Notation.Dot "rem" := {
    Notation.dot := rem;
  }.
End Rem.

Module RemAssign.
  Class Trait (Self : Set) (Rhs : option Set) : Set := {
    Rhs := defaultType Rhs Self;
    rem_assign : mut_ref Self -> Rhs -> unit;
  }.

  Global Instance Method_rem_assign `(Trait) : Notation.Dot "rem_assign" := {
    Notation.dot := rem_assign;
  }.
End RemAssign.

Module BitXor.
  Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
    Output := Output;
    Rhs := defaultType Rhs Self;
    bitxor : Self -> Rhs -> Output;
  }.

  Global Instance Method_bitxor `(Trait) : Notation.Dot "bitxor" := {
    Notation.dot := bitxor;
  }.
End BitXor.

Module BitXorAssign.
  Class Trait (Self : Set) (Rhs : option Set) : Set := {
    Rhs := defaultType Rhs Self;
    bitxor_assign : mut_ref Self -> Rhs -> unit;
  }.

  Global Instance Method_bitxor_assign `(Trait) : Notation.Dot "bitxor_assign" := {
    Notation.dot := bitxor_assign;
  }.
End BitXorAssign.

Module BitAnd.
  Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
    Output := Output;
    Rhs := defaultType Rhs Self;
    bitand : Self -> Rhs -> Output;
  }.

  Global Instance Method_bitand `(Trait) : Notation.Dot "bitand" := {
    Notation.dot := bitand;
  }.
End BitAnd.

Module BitAndAssign.
  Class Trait (Self : Set) (Rhs : option Set) : Set := {
    Rhs := defaultType Rhs Self;
    bitand_assign : mut_ref Self -> Rhs -> unit;
  }.

  Global Instance Method_bitand_assign `(Trait) : Notation.Dot "bitand_assign" := {
    Notation.dot := bitand_assign;
  }.
End BitAndAssign.

Module BitOr.
  Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
    Output := Output;
    Rhs := defaultType Rhs Self;
    bitor : Self -> Rhs -> Output;
  }.

  Global Instance Method_bitor `(Trait) : Notation.Dot "bitor" := {
    Notation.dot := bitor;
  }.
End BitOr.

Module BitOrAssign.
  Class Trait (Self : Set) (Rhs : option Set) : Set := {
    Rhs := defaultType Rhs Self;
    bitor_assign : mut_ref Self -> Rhs -> unit;
  }.

  Global Instance Method_bitor_assign `(Trait) : Notation.Dot "bitor_assign" := {
    Notation.dot := bitor_assign;
  }.
End BitOrAssign.

Module Shl.
  Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
    Output := Output;
    Rhs := defaultType Rhs Self;
    shl : Self -> Rhs -> Output;
  }.

  Global Instance Method_shl `(Trait) : Notation.Dot "shl" := {
    Notation.dot := shl;
  }.
End Shl.

Module ShlAssign.
  Class Trait (Self : Set) (Rhs : option Set) : Set := {
    Rhs := defaultType Rhs Self;
    shl_assign : mut_ref Self -> Rhs -> unit;
  }.

  Global Instance Method_shl_assign `(Trait) : Notation.Dot "shl_assign" := {
    Notation.dot := shl_assign;
  }.
End ShlAssign.

Module Shr.
  Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
    Output := Output;
    Rhs := defaultType Rhs Self;
    shr : Self -> Rhs -> Output;
  }.

  Global Instance Method_shr `(Trait) : Notation.Dot "shr" := {
    Notation.dot := shr;
  }.
End Shr.

Module ShrAssign.
  Class Trait (Self : Set) (Rhs : option Set) : Set := {
    Rhs := defaultType Rhs Self;
    shr_assign : mut_ref Self -> Rhs -> unit;
  }.

  Global Instance Method_shr_assign `(Trait) : Notation.Dot "shr_assign" := {
    Notation.dot := shr_assign;
  }.
End ShrAssign.

(* The trait implementations for [Z] are convenient but should be replaced
   by the implementations for the native types eventually. *)
Module Impl_Add_for_Z.
  Definition add : Z -> Z -> Z := Z.add.

  Global Instance Method_add : Notation.Dot "add" := {
    Notation.dot := add;
  }.

  Global Instance Add_for_Z : Add.Trait Z None := {
    add := add;
  }.
End Impl_Add_for_Z.

Module Impl_AddAssign_for_Z.
  Parameter add_assign : mut_ref Z -> Z -> unit.

  Global Instance Method_add_assign : Notation.Dot "add_assign" := {
    Notation.dot := add_assign;
  }.

  Global Instance AddAssign_for_Z : AddAssign.Trait Z None := {
    add_assign := add_assign;
  }.
End Impl_AddAssign_for_Z.

Module Impl_Sub_for_Z.
  Definition sub : Z -> Z -> Z := Z.sub.

  Global Instance Method_sub : Notation.Dot "sub" := {
    Notation.dot := sub;
  }.

  Global Instance Sub_for_Z : Sub.Trait Z None := {
    sub := sub;
  }.
End Impl_Sub_for_Z.

Module Impl_SubAssign_for_Z.
  Parameter sub_assign : mut_ref Z -> Z -> unit.

  Global Instance Method_sub_assign : Notation.Dot "sub_assign" := {
    Notation.dot := sub_assign;
  }.

  Global Instance SubAssign_for_Z : SubAssign.Trait Z None := {
    sub_assign := sub_assign;
  }.
End Impl_SubAssign_for_Z.

Module Impl_Mul_for_Z.
  Definition mul : Z -> Z -> Z := Z.mul.

  Global Instance Method_mul : Notation.Dot "mul" := {
    Notation.dot := mul;
  }.

  Global Instance Mul_for_Z : Mul.Trait Z None := {
    mul := mul;
  }.
End Impl_Mul_for_Z.

Module Impl_MulAssign_for_Z.
  Parameter mul_assign : mut_ref Z -> Z -> unit.

  Global Instance Method_mul_assign : Notation.Dot "mul_assign" := {
    Notation.dot := mul_assign;
  }.

  Global Instance MulAssign_for_Z : MulAssign.Trait Z None := {
    mul_assign := mul_assign;
  }.
End Impl_MulAssign_for_Z.

Module Impl_Div_for_Z.
  Definition div : Z -> Z -> Z := Z.div.

  Global Instance Method_div : Notation.Dot "div" := {
    Notation.dot := div;
  }.

  Global Instance Div_for_Z : Div.Trait Z None := {
    div := div;
  }.
End Impl_Div_for_Z.

Module Impl_DivAssign_for_Z.
  Parameter div_assign : mut_ref Z -> Z -> unit.

  Global Instance Method_div_assign : Notation.Dot "div_assign" := {
    Notation.dot := div_assign;
  }.

  Global Instance DivAssign_for_Z : DivAssign.Trait Z None := {
    div_assign := div_assign;
  }.
End Impl_DivAssign_for_Z.

Module Impl_Rem_for_Z.
  Definition rem : Z -> Z -> Z := Z.rem.

  Global Instance Method_rem : Notation.Dot "rem" := {
    Notation.dot := rem;
  }.

  Global Instance Rem_for_Z : Rem.Trait Z None := {
    rem := rem;
  }.
End Impl_Rem_for_Z.

Module Impl_RemAssign_for_Z.
  Parameter rem_assign : mut_ref Z -> Z -> unit.

  Global Instance Method_rem_assign : Notation.Dot "rem_assign" := {
    Notation.dot := rem_assign;
  }.

  Global Instance RemAssign_for_Z : RemAssign.Trait Z None := {
    rem_assign := rem_assign;
  }.
End Impl_RemAssign_for_Z.

Module Not.
  Class Trait {Output : Set} (Self : Set) : Set := {
    Output := Output;
    not : Self -> Output;
    }.
  Global Instance Method_snot `(Trait) : Notation.Dot "not" := {
    Notation.dot := not;
  }.
End Not.

(* Unary Operators *)
Module Neg.
  Class Trait {Output : Set} (Self : Set) : Set := {
    Output := Output;
    neg : Self -> Output;
    }.
  Global Instance Method_neg `(Trait) : Notation.Dot "neg" := {
    Notation.dot := neg;
  }.
End Neg.

(* 
pub trait Deref {
    type Target: ?Sized;

    // Required method
    fn deref(&self) -> &Self::Target;
}
*)
Module Deref.
  Class Trait (Self Target : Set) : Set := { 
    Target := Target;
    deref : ref Self -> Target; 
  }.
End Deref.

(* 
pub trait DerefMut: Deref {
    // Required method
    fn deref_mut(&mut self) -> &mut Self::Target;
} 
*)
Module DerefMut.
  Class Trait (Self Target : Set) : Set := {
    Target := Target;
    deref_mut : mut_ref Self -> Target;
  }.
End DerefMut.
