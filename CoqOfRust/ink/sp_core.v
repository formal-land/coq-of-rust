(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.

(* TODO: Implement the followings:
- [?] sr25519.Signature
- [x] crypto.AccountId32
- [x] sr25519.Pair
*)

Module sr25519.
  (* pub struct Pair(_); *)
  Unset Primitive Projections.
  Module Pair.
    Record t `{State.Trait} : Set := { }.
  End Pair.
  Global Set Primitive Projections.
  Definition Pair `{State.Trait} := M.Val Pair.t.

  (* pub struct Signature(pub [u8; 64]); *)
  (* NOTE: For now we use normal slice to approximate the array type *)
  Unset Primitive Projections.
  Module Signature.
    Record t `{State.Trait} : Set := { 
      _ : Slice u8;
    }.
  End Signature.
  Global Set Primitive Projections.
  Definition Signature `{State.Trait} := M.Val Signature.t.
End sr25519.

Module crypto.
  (* pub struct AccountId32(_); *)
  Unset Primitive Projections.
  Module AccountId32.
    Record t `{State.Trait} : Set := { }.
  End AccountId32.
  Global Set Primitive Projections.
  Definition AccountId32 `{State.Trait} := M.Val AccountId32.t.
End crypto.
