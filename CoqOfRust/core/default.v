Require Import CoqOfRust.lib.lib.

Module Impl_core_default_Default_for_u128.
  Definition Self : Ty.t := Ty.path "u128".
  
  (*
  fn default() -> $t {
      $v
  }
  *)
  Definition default (𝜏 : list Ty.t) (α : list Value.t) : M :=
    match 𝜏, α with
    | [], [] => M.pure (Value.Integer Integer.U128 0)
    | _, _ => M.impossible
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::default::Default"
      (* Self *) (Ty.path "u128")
      (* Trait polymorphic types *) []
      (* Instance *) [ ("default", InstanceField.Method default) ].
End Impl_core_default_Default_for_u128.
