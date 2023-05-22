Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(* 
[ ] Yeet
[ ] Range
[ ] RangeFrom
[ ] RangeFull
[ ] RangeInclusive
[ ] RangeTo
[ ] RangeToInclusive
 *)

(* ********ENUMS******** *)
(* 
[ ] GeneratorState
[ ] Bound
[ ] ControlFlow
*)

(* ********TRAITS******** *)
(* 
[ ] CoerceUnsized
[ ] DispatchFromDyn
[ ] FromResidual
[ ] Generator
[ ] OneSidedRange
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
[ ] Dere
[ ] DerefMut
[x] Div
[x] DivAssign
[ ] Drop
[ ] Fn
[ ] FnMut
[ ] FnOnce
[ ] Index
[ ] IndexMut
[x] Mul	
[x] MulAssign
[x] Neg
[x] Not
[ ] RangeBounds
[x] Rem
[x] RemAssign
[x] Shl
[x] ShlAssign
[x] Shr
[x] ShrAssign
[x] Sub
[x] SubAssign
*)

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