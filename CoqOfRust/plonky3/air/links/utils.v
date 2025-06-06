Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.air.utils.

(* TODO: refer to revm.revm_interpreter.gas.links.calc. 
or revm.revm_interpreter.instructions.links.host.
*)

(* 
pub fn pack_bits_le<R, Var, I>(iter: I) -> R
where
    R: PrimeCharacteristicRing,
    Var: Into<R> + Clone,
    I: DoubleEndedIterator<Item = Var>,
*)
Instance run_pack_bits_le
  {R Var I : Set} `{Link R} `{Link Var} `{Link I} 
  (* TODO: implement type dependencies *)
  (* TODO: fill run instances for types *)
  (* TODO: fill associated types for types *)
  (iter : I) :
  Run.Trait
    air.utils.pack_bits_le [] [ Φ F; Φ Var; Φ I; ] [ φ iter ]
    R.
Proof.
Admitted.

(* 
pub fn add2<AB: AirBuilder>(
    builder: &mut AB,
    a: &[AB::Var; 2],
    b: &[AB::Var; 2],
    c: &[AB::Expr; 2],
) 
*)
Instance run_add2
  {AB : Set} `{Link AB}
  {AB_types : AirBuilder.AssociatedTypes.t}
  {run_AirBuilder_for_AB : AirBuilder.Run AB}
  (builder : Ref.t Pointer.Kind.MutRef AB) 
  (a : array.t AB_types.(Var) {| Integer.value := 2 |})
  (b : array.t AB_types.(Var) {| Integer.value := 2 |})
  (c : array.t AB_types.(Expr) {| Integer.value := 2 |})
  :
  Run.Trait
    air.utils.run_add2 [] [ Φ AB ] [ φ builder; φ a; φ b; φ c ]
    unit.
Proof.
Admitted.

(* 
pub fn xor_32_shift<AB: AirBuilder>(
    builder: &mut AB,
    a: &[AB::Var; 2],
    b: &[AB::Var; 32],
    c: &[AB::Var; 32],
    shift: usize,
)
*)
Instance xor_32_shift
  {AB : Set} `{Link AB}
  {AB_types : AirBuilder.AssociatedTypes.t}
  {run_AirBuilder_for_AB : AirBuilder.Run AB}
  (builder : Ref.t Pointer.Kind.MutRef AB) 
  (a : array.t AB_types.(Var) {| Integer.value := 2 |})
  (b : array.t AB_types.(Var) {| Integer.value := 2 |})
  (c : array.t AB_types.(Expr) {| Integer.value := 2 |})
  (shift : Usize.t)
  :
  Run.Trait
    air.utils.run_add2 [] [ Φ AB ] [ φ builder; φ a; φ b; φ c; φ shift ]
    unit.
Proof.
Admitted.