Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.matrix.dense.

(* TODO: in the future, fix the type path with its correct name *)

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
    width : Usize.t;
  }.
  Arguments t : clear implicits.

  Parameter to_value : forall {T V : Set}, t T V -> Value.t.

  (* NOTE: It looks like Coq will take infinitely long time to find an 
  appropriate class for this instance *)
  (* NOTE: plonky3::matrix::dense::DenseMatrix *)
  Global Instance IsLink (T V : Set) : Link (t T V) := {
    Φ := Ty.apply (Ty.path "p3_matrix::dense::DenseMatrix") [ φ T; φ V ] [];
    φ := to_value;
  }.

  Definition of_ty (T' V' : Value.t) (T V : Set) :
    T' = φ T ->
    V' = φ V ->
    OfTy.t (Ty.apply (Ty.path "p3_matrix::dense::DenseMatrix") [ T' ; V' ] []).
  Proof. intros. eapply OfTy.Make with (A := t T V). now subst. Defined.
  Smpl Add eapply of_ty : of_ty.
End DenseMatrix.

(* 
pub type RowMajorMatrix<T> = DenseMatrix<T, Vec<T>>;
*)
Module RowMajorMatrix.
  Definition t (T : Set) := DenseMatrix.t T (list T).

  Global Instance IsLink (T : Set) : Link (t T) := {
    Φ := Ty.apply (Ty.path "p3_matrix::dense::RowMajorMatrix") [ φ T ] [];
    φ := to_value;
  }.

  Definition of_ty (T' : Value.t) (T V : Set) :
    T' = φ T ->
    OfTy.t (Ty.apply (Ty.path "p3_matrix::dense::RowMajorMatrix") [ T' ] []).
  Proof. intros. eapply OfTy.Make with (A := t T). now subst. Defined.
  Smpl Add eapply of_ty : of_ty.
End RowMajorMatrix.