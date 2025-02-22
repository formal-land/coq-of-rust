Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.lib.
Require Import CoqOfRust.links.M.
Require core.links.default.
Require revm.links.dependencies.
Import revm.links.dependencies.alloy_primitives.links.bytes_.
Require Import revm_precompile.interface.

Import Run.


(* 
    pub struct PrecompileOutput {
        /// Gas used by the precompile
        pub gas_used: u64,
        /// Output bytes
        pub bytes: Bytes,
    }
*)

Module PrecompileOutput.
  Record t : Set := {
    gas_used : U64.t;
    bytes : Bytes.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_precompile::interface::PrecompileOutput";
    φ x :=
        Value.StructRecord "revm_precompile::interface::PrecompileOutput" [
          ("gas_used", φ x.(gas_used));
          ("bytes", φ x.(bytes))
        ];
    }.

    Definition of_ty : OfTy.t (Ty.path "revm_precompile::interface::PrecompileOutput").
    Proof. eapply OfTy.Make with (A := t); reflexivity.
    Defined.
    Smpl Add apply of_ty : of_ty.

    Lemma of_value_with gas_used gas_used' bytes bytes' :
    gas_used' = φ gas_used ->
    bytes' = φ bytes ->
    Value.StructRecord "revm_precompile::interface::PrecompileOutput" [
      ("gas_used", gas_used');
      ("bytes", bytes')
    ] = φ (Build_t gas_used bytes).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value (gas_used : U64.t) gas_used' (bytes : Bytes.t) bytes' :
    gas_used' = φ gas_used ->
    bytes' = φ bytes ->
    OfValue.t (
      Value.StructRecord "revm_precompile::interface::PrecompileOutput" [
        ("gas_used", gas_used');
        ("bytes", bytes')
      ]
    ).
  Proof. econstructor; apply of_value_with; repeat eassumption.
  Defined.
  Smpl Add apply of_value : of_value.

End PrecompileOutput.

Module Impl_PrecompileOutput.
  Definition Self : Set := PrecompileOutput.t.

  (*
     pub fn new(gas_used: u64, bytes: Bytes) -> Self {
        Self { gas_used, bytes }
    }
  *)

  Definition run_new 
      (gas_used : U64.t) 
      (bytes : Bytes.t)
    : {{ interface.Impl_revm_precompile_interface_PrecompileOutput.new [] [] [φ gas_used; φ bytes] 🔽 PrecompileOutput.t }}.
  Proof.
    run_symbolic.
  Defined.
  Smpl Add apply run_new : run_closure.
End Impl_PrecompileOutput.
