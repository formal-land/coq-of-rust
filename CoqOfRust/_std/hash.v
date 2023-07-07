Require Import CoqOfRust.Monad.
Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust._std.marker.

(* ********STRUCTS******** *)
(* 
[x] BuildHasherDefault
[x] SipHasher(Deprecated) 
*)

(* pub struct BuildHasherDefault<H>(_); *)
Module BuildHasherDefault.
  Record t (H : Set) : Set := { }.
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
  finish : ref Self -> u64;

  (* fn write(&mut self, bytes: &[u8]); *)
  write : mut_ref Self -> ref (list u8) -> unit;

  (* fn write_u8(&mut self, i: u8) { ... } *)
  write_u8 : mut_ref Self -> u8 -> unit;

  (* fn write_u16(&mut self, i: u16) { ... } *)
  write_u16 : mut_ref Self -> u16 -> unit;

  (* fn write_u32(&mut self, i: u32) { ... } *)
  write_u32 : mut_ref Self -> u32 -> unit;

  (* fn write_u64(&mut self, i: u64) { ... } *)
  write_u64 : mut_ref Self -> u64 -> unit;

  (* fn write_u128(&mut self, i: u128) { ... } *)
  write_u128 : mut_ref Self -> u128 -> unit;

  (* fn write_usize(&mut self, i: usize) { ... } *)
  write_usize : mut_ref Self -> usize -> unit;

  (* fn write_i8(&mut self, i: i8) { ... } *)
  write_i8 : mut_ref Self -> i8 -> unit;

  (* fn write_i16(&mut self, i: i16) { ... } *)
  write_i16 : mut_ref Self -> i16 -> unit;

  (* fn write_i32(&mut self, i: i32) { ... } *)
  write_i32 : mut_ref Self -> i32 -> unit;

  (* fn write_i64(&mut self, i: i64) { ... } *)
  write_i64 : mut_ref Self -> i64 -> unit;

  (* fn write_i128(&mut self, i: i128) { ... } *)
  write_i128 : mut_ref Self -> i128 -> unit;

  (* fn write_isize(&mut self, i: isize) { ... } *)
  write_isize : mut_ref Self -> isize -> unit;

  (* fn write_length_prefix(&mut self, len: usize) { ... } *)
  write_length_prefix : mut_ref Self -> usize -> unit;

  (* fn write_str(&mut self, s: &str) { ... } *)
  write_str : mut_ref Self -> ref str;
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
  Class Trait (Self : Set) : Set := {
    hash `{State.Trait} {H : Set}
      `{Hasher : Hasher.Trait H}
      : ref Self -> mut_ref H -> M unit;


    (* @TODO 
    hash_slice (H : Set)
      `{Hasher.Trait H}
      (* `{Sized.Trait Self} *)
      : ref (list Self) -> M (mut_ref H);
     *)
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
        `{Hash.Trait T}
        `{Hasher.Trait Hasher}
        : ref Self -> T -> u64;
  }.
End BuilHasher.
