Require Import CoqOfRust.lib.lib.

Module arith.
  Module Add.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      add : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_add `(Trait) :
      Notation.Dot "add" := {
      Notation.dot := add;
    }.
  End Add.

  Module AddAssign.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      add_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_add_assign `(Trait) :
      Notation.Dot "add_assign" := {
      Notation.dot := add_assign;
    }.
  End AddAssign.

  Module Sub.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      sub : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_sub `(Trait) :
      Notation.Dot "sub" := {
      Notation.dot := sub;
    }.
  End Sub.

  Module SubAssign.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      sub_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_sub_assign `(Trait) :
      Notation.Dot "sub_assign" := {
      Notation.dot := sub_assign;
    }.
  End SubAssign.

  Module Mul.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      mul : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_mul `(Trait) :
      Notation.Dot "mul" := {
      Notation.dot := mul;
    }.
  End Mul.

  Module MulAssign.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      mul_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_mul_assign `(Trait) :
      Notation.Dot "mul_assign" := {
      Notation.dot := mul_assign;
    }.
  End MulAssign.

  Module Div.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      div : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_div `(Trait) :
      Notation.Dot "div" := {
      Notation.dot := div;
    }.
  End Div.

  Module DivAssign.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      div_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_div_assign `(Trait) :
      Notation.Dot "div_assign" := {
      Notation.dot := div_assign;
    }.
  End DivAssign.

  Module Rem.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      rem : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_rem `(Trait) :
      Notation.Dot "rem" := {
      Notation.dot := rem;
    }.
  End Rem.

  Module RemAssign.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      rem_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_rem_assign `(Trait) :
      Notation.Dot "rem_assign" := {
      Notation.dot := rem_assign;
    }.
  End RemAssign.

  Module BitXor.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      bitxor : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_bitxor `(Trait) :
      Notation.Dot "bitxor" := {
      Notation.dot := bitxor;
    }.
  End BitXor.

  Module BitXorAssign.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      bitxor_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_bitxor_assign `(Trait) :
      Notation.Dot "bitxor_assign" := {
      Notation.dot := bitxor_assign;
    }.
  End BitXorAssign.

  Module BitAnd.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      bitand : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_bitand `(Trait) :
      Notation.Dot "bitand" := {
      Notation.dot := bitand;
    }.
  End BitAnd.

  Module BitAndAssign.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      bitand_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_bitand_assign `(Trait) :
      Notation.Dot "bitand_assign" := {
      Notation.dot := bitand_assign;
    }.
  End BitAndAssign.

  Module BitOr.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      bitor : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_bitor `(Trait) :
      Notation.Dot "bitor" := {
      Notation.dot := bitor;
    }.
  End BitOr.

  Module BitOrAssign.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      bitor_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_bitor_assign `(Trait) :
      Notation.Dot "bitor_assign" := {
      Notation.dot := bitor_assign;
    }.
  End BitOrAssign.

  Module Shl.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      shl : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_shl `(Trait) :
      Notation.Dot "shl" := {
      Notation.dot := shl;
    }.
  End Shl.

  Module ShlAssign.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      shl_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_shl_assign `(Trait) :
      Notation.Dot "shl_assign" := {
      Notation.dot := shl_assign;
    }.
  End ShlAssign.

  Module Shr.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      shr : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_shr `(Trait) :
      Notation.Dot "shr" := {
      Notation.dot := shr;
    }.
  End Shr.

  Module ShrAssign.
    Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      shr_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_shr_assign `(Trait) :
      Notation.Dot "shr_assign" := {
      Notation.dot := shr_assign;
    }.
  End ShrAssign.

  Module Neg.
    Class Trait `{State.Trait} (Self : Set) : Type := {
      Output : Set;
      neg : Self -> M Output;
    }.

    Global Instance Method_neg `(Trait) :
      Notation.Dot "neg" := {
      Notation.dot := neg;
    }.
  End Neg.

  Module Not.
    Class Trait `{State.Trait} (Self : Set) : Type := {
      Output : Set;
      not : Self -> M Output;
    }.

    Global Instance Method_not `(Trait) :
      Notation.Dot "not" := {
      Notation.dot := not;
    }.
  End Not.
End arith.

Module Deref.
  Class Trait `{State.Trait} (Self : Set) {Target : Set} : Set := {
    Target := Target;
    deref : ref Self -> M (ref Target);
  }.

  Global Instance Method_deref `(Trait) :
    Notation.Dot "deref" := {
    Notation.dot := deref;
  }.
End Deref.

Module function.
  Module FnOnce.
    Class Trait `{State.Trait} (Self : Set) {Args : Set} : Type := {
      Output : Set;
      call_once : Self -> Args -> M Output;
    }.
  End FnOnce.

  Module FnMut.
    Class Trait `{State.Trait} (Self : Set) {Args : Set} : Type := {
      L0 :: FnOnce.Trait Self (Args := Args);
      call_mut : mut_ref Self -> Args -> M FnOnce.Output;
    }.
  End FnMut.
End function.

(* Module Impl_Add_for_i32. Section Impl_Add_for_i32.
  Context `{State.Trait}.

  Definition add (z1 z2 : i32) : M Z := M.pure (Z.add z1 z2).

  Global Instance Method_add : Notation.Dot "add" := {
    Notation.dot := add;
  }.

  Global Instance Add_for_Z :
      arith.Add.Trait Z (Rhs := arith.Add.Default.Rhs Z) := {
    add := add;
  }.
End Impl_Add_for_i32. End Impl_Add_for_i32.

Module Impl_AddAssign_for_Z.
  Context `{State.Trait}.

  Parameter add_assign : forall `{State.Trait}, mut_ref Z -> Z -> M unit.

  Global Instance Method_add_assign `{State.Trait} :
    Notation.Dot "add_assign" := {
    Notation.dot := add_assign;
  }.

  Global Instance AddAssign_for_Z :
    arith.AddAssign.Trait Z (Rhs := Z) := {
    add_assign `{State.Trait} := add_assign;
  }.
End Impl_AddAssign_for_Z.

Module Impl_Sub_for_Z.
  Definition sub `{State.Trait} (z1 z2 : Z) : M Z := M.pure (Z.sub z1 z2).

  Global Instance Method_sub `{State.Trait} : Notation.Dot "sub" := {
    Notation.dot := sub;
  }.

  Global Instance Sub_for_Z : arith.Sub.Trait Z (Rhs := Z) := {
    sub `{State.Trait} := sub;
  }.
End Impl_Sub_for_Z.

Module Impl_SubAssign_for_Z.
  Parameter sub_assign : forall `{State.Trait}, mut_ref Z -> Z -> M unit.

  Global Instance Method_sub_assign `{State.Trait} :
    Notation.Dot "sub_assign" := {
    Notation.dot := sub_assign;
  }.

  Global Instance SubAssign_for_Z :
    arith.SubAssign.Trait Z (Rhs := Z) := {
    sub_assign `{State.Trait} := sub_assign;
  }.
End Impl_SubAssign_for_Z.

Module Impl_Mul_for_Z.
  Definition mul `{State.Trait} (z1 z2 : Z) : M Z := M.pure (Z.mul z1 z2).

  Global Instance Method_mul `{State.Trait} : Notation.Dot "mul" := {
    Notation.dot := mul;
  }.

  Global Instance Mul_for_Z : arith.Mul.Trait Z (Rhs := Z) := {
    mul `{State.Trait} := mul;
  }.
End Impl_Mul_for_Z.

Module Impl_MulAssign_for_Z.
  Parameter mul_assign : forall `{State.Trait}, mut_ref Z -> Z -> M unit.

  Global Instance Method_mul_assign `{State.Trait} :
    Notation.Dot "mul_assign" := {
    Notation.dot := mul_assign;
  }.

  Global Instance MulAssign_for_Z :
    arith.MulAssign.Trait Z (Rhs := Z) := {
    mul_assign `{State.Trait} := mul_assign;
  }.
End Impl_MulAssign_for_Z.

Module Impl_Div_for_Z.
  Definition div `{State.Trait} (z1 z2 : Z) : M Z := M.pure (Z.div z1 z2).

  Global Instance Method_div `{State.Trait} : Notation.Dot "div" := {
    Notation.dot := div;
  }.

  Global Instance Div_for_Z : arith.Div.Trait Z (Rhs := Z) := {
    div `{State.Trait} := div;
  }.
End Impl_Div_for_Z.

Module Impl_DivAssign_for_Z.
  Parameter div_assign : forall `{State.Trait}, mut_ref Z -> Z -> M unit.

  Global Instance Method_div_assign `{State.Trait} :
    Notation.Dot "div_assign" := {
    Notation.dot := div_assign;
  }.

  Global Instance DivAssign_for_Z :
    arith.DivAssign.Trait Z (Rhs := Z) := {
    div_assign `{State.Trait} := div_assign;
  }.
End Impl_DivAssign_for_Z.

Module Impl_Rem_for_Z.
  Definition rem `{State.Trait} (z1 z2 : Z) : M Z := M.pure (Z.rem z1 z2).

  Global Instance Method_rem `{State.Trait} : Notation.Dot "rem" := {
    Notation.dot := rem;
  }.

  Global Instance Rem_for_Z : arith.Rem.Trait Z (Rhs := Z) := {
    rem `{State.Trait} := rem;
  }.
End Impl_Rem_for_Z.

Module Impl_RemAssign_for_Z.
  Parameter rem_assign : forall `{State.Trait}, mut_ref Z -> Z -> M unit.

  Global Instance Method_rem_assign `{State.Trait} :
    Notation.Dot "rem_assign" := {
    Notation.dot := rem_assign;
  }.

  Global Instance RemAssign_for_Z :
    arith.RemAssign.Trait Z (Rhs := Z) := {
    rem_assign `{State.Trait} := rem_assign;
  }.
End Impl_RemAssign_for_Z.

Module Impl_Neg_for_Z.
  Definition neg `{State.Trait} (z : Z) : M Z := M.pure (Z.opp z).

  Global Instance Method_neg `{State.Trait} : Notation.Dot "neg" := {
    Notation.dot := neg;
  }.

  Global Instance Neg_for_Z : arith.Neg.Trait Z := {
    neg `{State.Trait} := neg;
  }.
End Impl_Neg_for_Z. *)

Module Impl_Not_for_bool. Section Impl_Not_for_bool.
  Context `{State.Trait}.

  Definition not `{State.Trait} (b : bool) : M bool :=
    let* b := M.read b in
    M.alloc (negb b).

  Global Instance Method_not : Notation.Dot "not" := {
    Notation.dot := not;
  }.

  Global Instance Not_for_bool : arith.Not.Trait bool := {
    not := not;
  }.
End Impl_Not_for_bool. End Impl_Not_for_bool.

(** For now we implement the dereferencing operator on any types, as the
    identity. *)
Module Impl_Deref_for_any. Section Impl_Deref_for_any.
  Context `{State.Trait}.

  Definition deref {A : Set} (x : A) : M A := M.pure x.

  Global Instance Method_deref (A : Set) :
    Notation.Dot "deref" := {
    Notation.dot := deref (A := A);
  }.

  Global Instance Deref_for_any (A : Set) : Deref.Trait A := {
    deref := deref;
  }.
End Impl_Deref_for_any. End Impl_Deref_for_any.

Module drop.
  (*
  pub trait Drop {
      // Required method
      fn drop(&mut self);
  }
  *)
  Module Drop.
    Class Trait `{State.Trait} (Self : Set) : Set := {
      drop : mut_ref Self -> M unit;
    }.

    Global Instance Method_drop `(Trait) :
      Notation.Dot "drop" := {
      Notation.dot := drop;
    }.
  End Drop.
End drop.
