Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import pinocchio.instruction.
Require Import pinocchio.links.pubkey.

(*
pub struct AccountMeta<'a> {
    /// Public key of the account.
    pub pubkey: &'a Pubkey,

    /// Indicates whether the account is writable or not.
    pub is_writable: bool,

    /// Indicates whether the account signed the instruction or not.
    pub is_signer: bool,
}
*)
Module AccountMeta.
  Record t : Set := {
    pubkey : Ref.t Pointer.Kind.Ref Pubkey.t;
    is_writable : bool;
    is_signer : bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "pinocchio::instruction::AccountMeta";
    φ x :=
      Value.StructRecord "pinocchio::instruction::AccountMeta" [] [] [
        ("pubkey"     , φ x.(pubkey));
        ("is_writable", φ x.(is_writable));
        ("is_signer"  , φ x.(is_signer))
      ];
  }.

  Definition of_ty : OfTy.t (Ty.path "pinocchio::instruction::AccountMeta").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End AccountMeta.

(*
pub struct Instruction<'a, 'b, 'c, 'd>
where
    'a: 'b,
{
    /// Public key of the program.
    pub program_id: &'c Pubkey,

    /// Data expected by the program instruction.
    pub data: &'d [u8],

    /// Metadata describing accounts that should be passed to the program.
    pub accounts: &'b [AccountMeta<'a>],
}
*)
Module Instruction.
  Record t : Set := {
    program_id : Ref.t Pointer.Kind.Ref Pubkey.t;
    data: Ref.t Pointer.Kind.Ref (list U8.t);
    accounts: Ref.t Pointer.Kind.Ref (list AccountMeta.t);
  }.

  Global Instance IsLink : Link t :=
  { Φ := Ty.path "pinocchio::instruction::Instruction";
    φ x :=
      Value.StructRecord "pinocchio::instruction::Instruction" [] [] [
        ("program_id", φ x.(program_id));
        ("data"      , φ x.(data));
        ("accounts"  , φ x.(accounts))
      ];
  }.

  Definition of_ty : OfTy.t (Ty.path "pinocchio::instruction::Instruction").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End Instruction.