Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.core.marker.

(* ********STRUCTS******** *)
(* 
[x] BuildHasherDefault
[x] SipHasher(Deprecated) 
*)

(* pub struct BuildHasherDefault<H>(_); *)
Module BuildHasherDefault.
  Parameter t : forall (H : Set), Set.
End BuildHasherDefault.
Definition BuildHasherDefault := BuildHasherDefault.t.


(* ********TRAITS******** *)
(* 
[x] BuildHasher
[x] Hash
[x] Hasher 
*)

(* 
pub trait Hasher {
  // ...
}
*)
Module Hasher.
  Class Trait (Self : Set) : Set := {
  (* fn finish(&self) -> u64; *)
  finish : ref Self -> u64.t;

  (* fn write(&mut self, bytes: &[u8]); *)
  write : mut_ref Self -> ref (list u8.t) -> unit;

  (* fn write_u8(&mut self, i: u8) { ... } *)
  write_u8 : mut_ref Self -> u8.t -> unit;

  (* fn write_u16(&mut self, i: u16) { ... } *)
  write_u16 : mut_ref Self -> u16.t -> unit;

  (* fn write_u32(&mut self, i: u32) { ... } *)
  write_u32 : mut_ref Self -> u32.t -> unit;

  (* fn write_u64(&mut self, i: u64) { ... } *)
  write_u64 : mut_ref Self -> u64.t -> unit;

  (* fn write_u128(&mut self, i: u128) { ... } *)
  write_u128 : mut_ref Self -> M.Val u128.t -> unit;

  (* fn write_usize(&mut self, i: usize) { ... } *)
  write_usize : mut_ref Self -> usize.t -> unit;

  (* fn write_i8(&mut self, i: i8) { ... } *)
  write_i8 : mut_ref Self -> i8.t -> unit;

  (* fn write_i16(&mut self, i: i16) { ... } *)
  write_i16 : mut_ref Self -> i16.t -> unit;

  (* fn write_i32(&mut self, i: i32) { ... } *)
  write_i32 : mut_ref Self -> i32.t -> unit;

  (* fn write_i64(&mut self, i: i64) { ... } *)
  write_i64 : mut_ref Self -> i64.t -> unit;

  (* fn write_i128(&mut self, i: i128) { ... } *)
  write_i128 : mut_ref Self -> i128.t -> unit;

  (* fn write_isize(&mut self, i: isize) { ... } *)
  write_isize : mut_ref Self -> isize.t -> unit;

  (* fn write_length_prefix(&mut self, len: usize) { ... } *)
  write_length_prefix : mut_ref Self -> usize.t -> unit;

  (* fn write_str(&mut self, s: &str) { ... } *)
  write_str : mut_ref Self -> ref str.t;
  }.
End Hasher.

(* 
pub trait Hash {
    // Required method
    fn hash<H>(&self, state: &mut H)
       where H: Hasher;

    // Provided method
    fn hash_slice<H>(data: &[Self], state: &mut H)
       where H: Hasher,
             Self: Sized { ... }
}
*)
Module Hash.
  Module Required.
    Class Trait (Self : Set) : Set := {
      hash {H : Set} : ref Self -> mut_ref H -> M unit;
      hash_slice :
        Datatypes.option (
          forall (H : Set),
          ref (slice Self) -> mut_ref H -> M unit
        );
    }.
  End Required.

  Module Provided.
    Parameter hash_slice :
      forall {Self : Set} {H : Set},
      ref (slice Self) -> mut_ref H -> M unit.
  End Provided.

  Class Trait (Self : Set) : Set := {
    hash {H : Set} : ref Self -> mut_ref H -> M unit;
    hash_slice {H : Set} :
      ref (slice Self) -> mut_ref H -> M unit;
  }.

  Global Instance From_Required {Self : Set}
      {H0 : Required.Trait Self} :
      Trait Self := {
    hash {H : Set} := Required.hash (H := H);
    hash_slice {H : Set} := Provided.hash_slice (H := H);
  }.
End Hash.

(* 
pub trait BuildHasher {
    type Hasher: Hasher;

    // Required method
    fn build_hasher(&self) -> Self::Hasher;

    // Provided method
    fn hash_one<T>(&self, x: T) -> u64
       where T: Hash,
             Self: Sized,
             Self::Hasher: Hasher { ... }
}
*)
Module BuilHasher.
  Class Trait (Self Hasher : Set) 
    `{Hasher.Trait Hasher}
    : Set := { 
      Hasher := Hasher;
      build_hasher : ref Self -> Hasher;
      hash_one (T : Set) 
        : ref Self -> T -> u64.t;
  }.
End BuilHasher.
