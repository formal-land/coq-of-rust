Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require CoqOfRust.examples.default.examples.custom.micro_bank.

Import simulations.M.Notations.

Module u32.
  Inductive t : Set :=
  | Make : Z -> t.

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "u32";
    φ '(Make x) := Value.Integer Integer.U32 x;
  }.
End u32.

Module i32.
  Inductive t : Set :=
  | Make : Z -> t.

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "i32";
    φ '(Make x) := Value.Integer Integer.U32 x;
  }.
End i32.

Module usize.
  Inductive t : Set :=
  | Make : Z -> t.

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "usize";
    φ '(Make x) := Value.Integer Integer.Usize x;
  }.
End usize.

Module Vec.
  Inductive t (A : Set) : Set :=
  | Make : list A -> t A.
  Arguments Make {A} _.

  Global Instance IsToValue {A : Set} `{ToValue A} : ToValue (t A) := {
    Φ :=
      Ty.apply (Ty.path "alloc::vec::Vec") [
        Φ A;
        Ty.path "alloc::alloc::Global"
      ];
    φ '(Make x) := Value.Array (List.map φ x);
  }.
End Vec.

Module Impl_Vec_T.
  (* pub fn len(&self) -> usize *)
  Definition len {A : Set} (v : Vec.t A) : usize.t :=
    let 'Vec.Make v := v in
    usize.Make (Z.of_nat (List.length v)).
End Impl_Vec_T.

(*
pub trait Index<Idx: ?Sized> {
    type Output: ?Sized;

    // Required method
    fn index(&self, index: Idx) -> &Self::Output;
}
*)
Module Index.
  Class Trait (Self Idx Output : Set) : Set := {
    index : Self -> Idx -> M? Output;
  }.
End Index.

Definition get_at_index (vector : Vec.t i32.t) (index : usize.t) : i32.t :=
  let 'Vec.Make v := vector in
  let 'usize.Make i := index in
  match List.nth_error v (Z.to_nat i) with
  | Some x => x
  | None => i32.Make 0
  end.

(* Module Bank.
  Record t : Set := {
    accounts : Vec.t u32.t;
  }.

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "micro_bank::Bank";
    φ x :=
      Value.StructRecord "micro_bank::Bank" [("accounts", φ x.(accounts))];
  }.
End Bank.

Module Impl_micro_bank_Bank.
  Definition transfer
      (bank : Bank.t)
      (from : usize.t)
      (to : usize.t)
      (amount : u32.t)
      : Bank.t := *)

