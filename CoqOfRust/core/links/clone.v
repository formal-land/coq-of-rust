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
  Record RunImpl (Self : Set) (Self_ty : Ty.t) `{ToValue Self} : Set := {
    clone : {clone @
      IsTraitMethod.t "core::clone::Clone" Self_ty [] "clone" clone *
      forall (self : Ref.t Self),
        {{
          clone [] [ φ self ] ⇓
          fun (v : Self) => inl (φ v)
        }}
    };
    (* TODO: add [clone_from] *)
  }.
End Clone.
