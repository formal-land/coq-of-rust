Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.matrix.dense.

(* TODO:
  - in the future, check the detail of the proof
*)

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

  Global Instance IsLink (T V : Set) `{Link T} `{Link V} : Link (t T V) := {
    Φ := Ty.apply (Ty.path "p3_matrix::dense::DenseMatrix") [] [ Φ T; Φ V ];
    φ := to_value;
  }.

  Definition of_ty (T_ty V_ty : Ty.t) :
    OfTy.t T_ty -> OfTy.t V_ty ->
    OfTy.t (Ty.apply (Ty.path "p3_matrix::dense::DenseMatrix") [] [ T_ty ; V_ty ]).
  (* TODO: check the proof in the future *)
  Proof. intros [T] [V]. eapply OfTy.Make with (A := t T V). now subst. Defined.
  Smpl Add eapply of_ty : of_ty.
End DenseMatrix.

(* 
pub type RowMajorMatrix<T> = DenseMatrix<T, Vec<T>>;
*)
Module RowMajorMatrix.
  Definition t (T : Set) := DenseMatrix.t T (list T).

  Parameter to_value : forall {T : Set}, t T -> Value.t.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "p3_matrix::dense::RowMajorMatrix") [] [ Φ T ];
    φ := to_value;
  }.

  Definition of_ty (T_ty : Ty.t) :
    OfTy.t T_ty -> 
    OfTy.t (Ty.apply (Ty.path "p3_matrix::dense::RowMajorMatrix") [] [ T_ty ]).
  Proof. intros [T]. eapply OfTy.Make with (A := t T). now subst. Defined.
  Smpl Add eapply of_ty : of_ty.
End RowMajorMatrix.