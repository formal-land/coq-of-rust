Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import plonky3.commit_539bbc84.keccak_air.constants.

(*
pub(crate) const R: [[u8; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];
*)
Definition R : array.t (array.t U8.t {| Integer.value := 5 |}) {| Integer.value := 5 |} :=
  {|
    array.value := [
      {| array.value := List.map (Integer.Build_t IntegerKind.U8) [0; 36; 3; 41; 18] |};
      {| array.value := List.map (Integer.Build_t IntegerKind.U8) [1; 44; 10; 45; 2] |};
      {| array.value := List.map (Integer.Build_t IntegerKind.U8) [62; 6; 43; 15; 61] |};
      {| array.value := List.map (Integer.Build_t IntegerKind.U8) [28; 55; 25; 21; 56] |};
      {| array.value := List.map (Integer.Build_t IntegerKind.U8) [27; 20; 39; 8; 14] |}
    ]
  |}.

Instance run_value_R :
  Run.Trait constants.value_R [] [] []
    (Ref.t Pointer.Kind.Raw (array.t (array.t U8.t {| Integer.value := 5 |}) {| Integer.value := 5 |})).
Proof.
  constructor.
  run_symbolic.
Defined.

(*
pub const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];
*)
Definition RC : array.t U64.t {| Integer.value := 24 |} :=
  {|
    array.value := List.map (Integer.Build_t IntegerKind.U64) [
      0x0000000000000001;
      0x0000000000008082;
      0x800000000000808A;
      0x8000000080008000;
      0x000000000000808B;
      0x0000000080000001;
      0x8000000080008081;
      0x8000000000008009;
      0x000000000000008A;
      0x0000000000000088;
      0x0000000080008009;
      0x000000008000000A;
      0x000000008000808B;
      0x800000000000008B;
      0x8000000000008089;
      0x8000000000008003;
      0x8000000000008002;
      0x8000000000000080;
      0x000000000000800A;
      0x800000008000000A;
      0x8000000080008081;
      0x8000000000008080;
      0x0000000080000001;
      0x8000000080008008
    ]
  |}.

Instance run_value_RC :
  Run.Trait constants.value_RC [] [] []
    (Ref.t Pointer.Kind.Raw (array.t U64.t {| Integer.value := 24 |})).
Proof.
  constructor.
  run_symbolic.
  { exact RC. }
  { reflexivity. }
Defined.

(* const RC_BITS: [[u8; 64]; 24] *)
Definition RC_BITS : array.t (array.t U8.t {| Integer.value := 64 |}) {| Integer.value := 24 |} :=
  {|
    array.value :=
      List.map
        (fun x => {|
          array.value :=
            List.map
              (fun i => {| Integer.value := Z.b2z (Z.testbit x.(Integer.value) (Z.of_nat i)) |})
              (List.seq 0 64)
        |})
        RC.(array.value)
  |}.

Instance run_value_RC_BITS :
  Run.Trait constants.value_RC_BITS [] [] []
    (Ref.t Pointer.Kind.Raw (array.t (array.t U8.t {| Integer.value := 64 |}) {| Integer.value := 24 |})).
Proof.
  constructor.
  run_symbolic.
  { exact RC_BITS. }
  { reflexivity. }
Defined.

(* pub(crate) const fn rc_value_bit(round: usize, bit_index: usize) -> u8 *)
Instance run_value_rc_value_bit (round bit_index : Usize.t) :
  Run.Trait constants.rc_value_bit [] [] [ φ round; φ bit_index ] U8.t.
Proof.
  constructor.
  run_symbolic.
Defined.
