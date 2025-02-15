Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

(* pub const BLOCK_HASH_HISTORY: u64 = 256; *)
Definition BLOCK_HASH_HISTORY : U64.t := {|
  Integer.value := 256;
|}.

(* pub const BLOCKHASH_SERVE_WINDOW: usize = 8192; *)
Definition BLOCKHASH_SERVE_WINDOW : Usize.t := {|
  Integer.value := 8192;
|}.
