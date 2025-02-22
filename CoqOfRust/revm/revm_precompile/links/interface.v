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
    Φ := Ty.path "revm_precompile::PrecompileOutput";
    φ x :=
        Value.StructRecord "revm_precompile::PrecompileOutput" [
          ("gas_used", φ x.(gas_used));
          ("bytes", φ x.(bytes))
        ];
    }.

  

End PrecompileOutput.