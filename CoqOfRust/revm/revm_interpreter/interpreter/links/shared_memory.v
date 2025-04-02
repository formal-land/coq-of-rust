Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloc.links.alloc.
Require Import alloc.vec.links.mod.
Require Import core.links.array.
Require Import core.links.option.
Require Import core.num.links.mod.
Require Import revm_interpreter.interpreter.shared_memory.

Import Impl_usize.

(*
  pub struct SharedMemory {
      buffer: Vec<u8>,
      checkpoints: Vec<usize>,
      last_checkpoint: usize,
      memory_limit: u64,
  }
*)
Module SharedMemory.
  Record t : Set := {
    buffer : Vec.t U8.t Global.t;
    checkpoints : Vec.t Usize.t Global.t;
    last_checkpoint : Usize.t;
    memory_limit : option U64.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::shared_memory::SharedMemory";
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::shared_memory::SharedMemory" [
        ("buffer", φ x.(buffer));
        ("checkpoints", φ x.(checkpoints));
        ("last_checkpoint", φ x.(last_checkpoint));
        ("memory_limit", φ x.(memory_limit))
      ];
  }.
End SharedMemory.

(* pub const fn num_words(len: usize) -> usize *)
Instance run_num_words (len : Usize.t) :
  Run.Trait
    interpreter.shared_memory.num_words [] [] [ φ len ]
    Usize.t.
Proof.
  constructor.
  run_symbolic.
Defined.
