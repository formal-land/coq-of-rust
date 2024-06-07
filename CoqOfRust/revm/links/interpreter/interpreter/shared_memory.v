Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.core.links.option.
Require Import CoqOfRust.core.links.array.

(*
  /// A sequential memory shared between calls, which uses
  /// a `Vec` for internal representation.
  /// A [SharedMemory] instance should always be obtained using
  /// the `new` static method to ensure memory safety.
  #[derive(Clone, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct SharedMemory {
      /// The underlying buffer.
      buffer: Vec<u8>,
      /// Memory checkpoints for each depth.
      /// Invariant: these are always in bounds of `data`.
      checkpoints: Vec<usize>,
      /// Invariant: equals `self.checkpoints.last()`
      last_checkpoint: usize,
      /// Memory limit. See [`CfgEnv`](revm_primitives::CfgEnv).
      #[cfg(feature = "memory_limit")]
      memory_limit: u64,
  }
*)

Module SharedMemory.
  Record t : Set := {
    buffer : list Z;
    checkpoints : list Z;
    last_checkpoint : Z;
    memory_limit : option Z;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter::shared_memory::SharedMemory";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::shared_memory::SharedMemory" [
        ("buffer", φ x.(buffer));
        ("checkpoints", φ x.(checkpoints));
        ("last_checkpoint", φ x.(last_checkpoint));
        ("memory_limit", φ x.(memory_limit))
      ];
  }.
End SharedMemory.
