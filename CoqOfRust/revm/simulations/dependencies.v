Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.revm.links.dependencies.

(*Module U256.
  Import links.dependencies.U256.

  Definition limb_size : Z := 64.

  Definition BITS : Z := 256.
  Definition LIMBS : Z := 4.

  Definition ZERO : t := 0.
  Definition from : Z -> t := id.

  Definition u64_try_from (a : t) : option Z :=
    if a <? 2 ^ BITS
    then Some a
    else None.

  Definition eq : t -> t -> bool := Z.eqb.
  Definition lt : t -> t -> bool := Z.ltb.
  Definition gt : t -> t -> bool := Z.gtb.
  Definition le : t -> t -> bool := Z.leb.
  Definition ge : t -> t -> bool := Z.geb.

  Definition wrapping_add (a b : t) : t := (a + b) mod size.
  Definition wrapping_sub (a b : t) : t := (a - b) mod size.
  Definition wrapping_mul (a b : t) : t := (a * b) mod size.
  Definition wrapping_div (a b : t) : t := (Z.quot a b) mod size.
  Definition wrapping_rem (a b : t) : t := (Z.rem a b) mod size.
  Definition wrapping_pow (a b : t) : t := (Z.pow a b) mod size.

  Definition log2floor : t -> Z := Z.log2.

  Definition add_mod (a b m : t) : t := ((a + b) mod m) mod size.
  Definition mul_mod (a b m : t) : t := ((a * b) mod m) mod size.

  Definition checked_add (a b : t) : option t :=
    let r := (a + b)%Z in
    if r <? 2 ^ BITS
    then Some r
    else None.
  
  Definition checked_mul (a b : t) : option t :=
    let r := (a * b)%Z in
    if r <? 2 ^ BITS
    then Some r
    else None.

  (* bit operations *)
  Definition bit : t -> Z -> bool := Z.testbit.
  Definition not : t -> t := Z.lnot.
  Definition and : t -> t -> t := Z.land.
  Definition or  : t -> t -> t := Z.lor.
  Definition shl : t -> Z -> t := Z.shiftl.
  Definition shr : t -> Z -> t := Z.shiftr.    

  Definition as_limbs (a : t) : list Z :=
    List.map
      (fun n => (Z.shiftr a (limb_size * Z.of_nat n)) mod (2 ^ limb_size))
      (List.seq 0 (Z.to_nat LIMBS)).
End U256.
*)
