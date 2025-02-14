Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.revm.links.dependencies.

(*
  /// Create scheme.
  #[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub enum CreateScheme {
      /// Legacy create scheme of `CREATE`.
      Create,
      /// Create scheme of `CREATE2`.
      Create2 {
          /// Salt.
          salt: U256,
      },
  }
*)

Module CreateScheme.
  Inductive t : Set :=
  | Create
  | Create2 : U256.t -> t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_primitives::env::CreateScheme";
    φ x :=
      match x with
      | Create => Value.StructTuple "revm_primitives::env::CreateScheme::Create" []
      | Create2 x => Value.StructTuple "revm_primitives::env::CreateScheme::Create2" [φ x]
      end;
  }.
End CreateScheme.
