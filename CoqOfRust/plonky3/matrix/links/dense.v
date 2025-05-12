(* TODO: RowMajorMatrix *)

(* 
pub struct DenseMatrix<T, V = Vec<T>> {
    pub values: V,
    pub width: usize,
    _phantom: PhantomData<T>,
}
*)
Module DenseMatrix.
  Parameter T : Type.
  Parameter V : Type.

  (* TODO: figure out better and uniformed way to express this *)
  Parameter t : T -> V -> Set.

  Record t : Set :- {
    values : V;
    width : usize.t;
    (* TODO: Do we need to import PhantomData type from core lib? *)
    _phantom : Set;
  }
End DenseMatrix.

(* 
pub type RowMajorMatrix<T> = DenseMatrix<T, Vec<T>>;
*)
Module RowMajorMatrix.
  Parameter T : Set.

  Definition t := DenseMatrix.t T (list T).
End RowMajorMatrix.