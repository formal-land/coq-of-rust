Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloc.links.alloc.
Require Import alloc.vec.links.mod.
Require Import plonky3.matrix.dense.

(* 
pub struct DenseMatrix<T, V = Vec<T>> {
    pub values: V,
    pub width: usize,
    _phantom: PhantomData<T>,
}
*)
Module DenseMatrix.
  Record t {T V : Set} : Set := {
    values : V;
    width : Usize.t;
  }.
  Arguments t : clear implicits.

  Global Instance IsLink (T V : Set) `{Link T} `{Link V} : Link (t T V) := {
    Φ := Ty.apply (Ty.path "p3_matrix::dense::DenseMatrix") [] [ Φ T; Φ V ];
    φ x := Value.StructRecord "p3_matrix::dense::DenseMatrix" [] [] [
      ("values", φ x.(values));
      ("width", φ x.(width))
    ];
  }.

  Definition of_ty (T' V' : Ty.t) :
    OfTy.t T' ->
    OfTy.t V' ->
    OfTy.t (Ty.apply (Ty.path "p3_matrix::dense::DenseMatrix") [] [ T'; V']).
  Proof. intros [T] [V]. eapply OfTy.Make with (A := t T V). now subst. Defined.
  Smpl Add eapply of_ty : of_ty.
End DenseMatrix.

(* 
pub type RowMajorMatrix<T> = DenseMatrix<T, Vec<T>>;
*)
Module RowMajorMatrix.
  Definition t (T : Set) := DenseMatrix.t T (Vec.t Global.t T).
End RowMajorMatrix.
