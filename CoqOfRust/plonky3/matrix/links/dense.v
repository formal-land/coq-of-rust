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
    width : Usize.t;
  }.
  Arguments t : clear implicits.

  Parameter to_value : forall {T V : Set}, t T V -> Value.t.

  (* NOTE: It looks like Coq will take infinitely long time to find an 
  appropriate class for this instance *)
  Global Instance IsLink (T V : Set) : Link (t T V) := {
    Φ := Ty.apply (Ty.path "plonky3::matrix::dense::DenseMatrix") [ φ T; φ V ] [];
    φ := to_value;
  }.

  Definition of_ty (T' V' : Value.t) (T V : Set) :
    T' = φ T ->
    V' = φ V ->
    OfTy.t (Ty.apply (Ty.path "plonky3::matrix::dense::DenseMatrix") [ T' ; V' ] []).
  Proof. intros. eapply OfTy.Make with (A := t T V). now subst. Defined.
  Smpl Add eapply of_ty : of_ty.
End DenseMatrix.

(* 
pub type RowMajorMatrix<T> = DenseMatrix<T, Vec<T>>;
*)
Module RowMajorMatrix.
  Definition t (T : Set) := DenseMatrix.t T (list T).
End RowMajorMatrix.