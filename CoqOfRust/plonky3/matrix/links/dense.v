Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.matrix.dense.

(* 
pub struct DenseMatrix<T, V = Vec<T>> {
    pub values: V,
    pub width: usize,
    _phantom: PhantomData<T>,
}
*)
Module DenseMatrix.
  Record t (T V : Set) : Set := {
    values : V;
    width : usize.t;
    _phantom : Set;
  }.

  Parameter to_value : forall {T V : Set}, t T V -> Value.t.

  Global Instance IsLink (T V : Set) : Link (t T V) := {
    Φ := Ty.apply (Ty.path "plonky3::matrix::dense::DenseMatrix") [ φ T; φ V ] [];
    φ := to_value;
  }.

  (* TODO: define `of_ty` *)
  (* Definition of_ty (N' : Value.t) (N: Usize.t) :
    N' = φ N ->
    OfTy.t (Ty.apply (Ty.path "alloy_primitives::bits::fixed::FixedBytes") [ N' ] []).
  Proof.
    intros.
    eapply OfTy.Make with (A := t N).
    subst.
    reflexivity.
  Defined.
  Smpl Add eapply of_ty : of_ty. *)

End DenseMatrix.

(* 
pub type RowMajorMatrix<T> = DenseMatrix<T, Vec<T>>;
*)
Module RowMajorMatrix.
  Definition t (T : Set) := DenseMatrix.t T (list T).
End RowMajorMatrix.