Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Import Run.

(*
    pub trait Clone: Sized {
        fn clone(&self) -> Self;

        fn clone_from(&mut self, source: &Self) {
            *self = source.clone()
        }
    }
*)
Module Clone.
  Definition Run_clone (Self : Set) (Self_ty : Ty.t) `{ToValue Self} : Set :=
    {clone @
      IsTraitMethod.t "core::clone::Clone" Self_ty [] "clone" clone *
      forall (self : Ref.t Self),
        {{
          clone [] [ φ self ] ⇓
          fun (v : Self) => inl (φ v)
        }}
    }.

  Record RunImpl (Self : Set) (Self_ty : Ty.t) `{ToValue Self} : Set := {
    clone : Run_clone Self Self_ty;
    (* TODO: add [clone_from] *)
  }.
End Clone.
