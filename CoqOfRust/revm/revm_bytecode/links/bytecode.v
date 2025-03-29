Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

(* Module Bytecode.
  Inductive t : Set :=
  | LegacyAnalyzed
    (_ : revm_bytecode.legacy.links.analyzed.LegacyAnalyzedBytecode.t)
  | Eof
    (_ : alloc.links.sync.Arc.t revm_bytecode.links.eof.Eof.t alloc.links.alloc.Global.t)
  | Eip7702
    (_ : revm_bytecode.links.eip7702.Eip7702Bytecode.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "bytecode::Bytecode";
    φ x :=
      match x with
      | LegacyAnalyzed γ0 =>
        Value.StructTuple "bytecode::Bytecode::LegacyAnalyzed" [
          φ γ0
        ]
      | Eof γ0 =>
        Value.StructTuple "bytecode::Bytecode::Eof" [
          φ γ0
        ]
      | Eip7702 γ0 =>
        Value.StructTuple "bytecode::Bytecode::Eip7702" [
          φ γ0
        ]
      end
  }.
End Bytecode. *)
