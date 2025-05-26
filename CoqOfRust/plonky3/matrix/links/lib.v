Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.ops.links.deref.
Require Import plonky3.matrix.lib.

(*
pub struct Dimensions {
    pub width: usize,
    pub height: usize,
}
*)
Module Dimensions.
  Record t : Set := {
    width : Usize.t;
    height : Usize.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "p3_matrix::Dimensions";
    φ x := Value.StructRecord "p3_matrix::Dimensions" [] [] [
      ("width", φ x.(width));
      ("height", φ x.(height))
    ];
  }.
End Dimensions.

(*
pub trait Matrix<T: Send + Sync>: Send + Sync {
    fn width(&self) -> usize;
    fn height(&self) -> usize;

    fn dimensions(&self) -> Dimensions;

    fn get(&self, r: usize, c: usize) -> T;

    type Row<'a>: Iterator<Item = T> + Send + Sync
    where
        Self: 'a;

    fn row(&self, r: usize) -> Self::Row<'_>;

    fn rows(&self) -> impl Iterator<Item = Self::Row<'_>>;

    fn par_rows(&self) -> impl IndexedParallelIterator<Item = Self::Row<'_>>;

    fn row_slice(&self, r: usize) -> impl Deref<Target = [T]>;

    fn first_row(&self) -> Self::Row<'_>;

    fn last_row(&self) -> Self::Row<'_>;

    fn to_row_major_matrix(self) -> RowMajorMatrix<T>
    where
        Self: Sized,
        T: Clone,

    fn horizontally_packed_row<'a, P>(
        &'a self,
        r: usize,
    ) -> (
        impl Iterator<Item = P> + Send + Sync,
        impl Iterator<Item = T> + Send + Sync,
    )
    where
        P: PackedValue<Value = T>,
        T: Clone + 'a,

    fn padded_horizontally_packed_row<'a, P>(
        &'a self,
        r: usize,
    ) -> impl Iterator<Item = P> + Send + Sync
    where
        P: PackedValue<Value = T>,
        T: Clone + Default + 'a,

    fn par_horizontally_packed_rows<'a, P>(&'a self) -> impl IndexedParallelIterator<Item = (impl Iterator<Item = P> + Send + Sync, impl Iterator<Item = T> + Send + Sync)>
    where
        P: PackedValue<Value = T>,
        T: Clone + 'a,

    fn par_padded_horizontally_packed_rows<'a, P>(
        &'a self,
    ) -> impl IndexedParallelIterator<Item = impl Iterator<Item = P> + Send + Sync>
    where
        P: PackedValue<Value = T>,
        T: Clone + Default + 'a,

    fn vertically_packed_row<P>(&self, r: usize) -> impl Iterator<Item = P>
    where
        T: Copy,
        P: PackedValue<Value = T>,
    ;

    fn vertically_packed_row_pair<P>(&self, r: usize, step: usize) -> Vec<P>
    where
        T: Copy,
        P: PackedValue<Value = T>,

    fn vertically_strided(self, stride: usize, offset: usize) -> VerticallyStridedMatrixView<Self>
    where
        Self: Sized,

    fn columnwise_dot_product<EF>(&self, v: &[EF]) -> Vec<EF>
    where
        T: Field,
        EF: ExtensionField<T>,

    fn rowwise_packed_dot_product<EF>(
        &self,
        vec: &[EF::ExtensionPacking],
    ) -> impl IndexedParallelIterator<Item = EF>
    where
        T: Field,
        EF: ExtensionField<T>,
}
*)
Module Matrix.
  Definition trait (Self T : Set) `{Link Self} `{Link T} : TraitMethod.Header.t :=
    ("p3_matrix::Matrix", [], [Φ T], Φ Self).

  Module AssociatedTypes.
    Record t : Type := {
      Row : Set;
      Synthetic : Set;
      Synthetic1 : Set;
      Synthetic2 : Set;
    }.

    Class AreLinks (types : t) : Set := {
      H_Row : Link types.(Row);
      H_Synthetic : Link types.(Synthetic);
      H_Synthetic1 : Link types.(Synthetic1);
      H_Synthetic2 : Link types.(Synthetic2);
    }.

    Global Instance IsLinkRow (types : t) (H : AreLinks types) : Link types.(Row) :=
      H.(H_Row _).
    Global Instance IsLinkSynthetic (types : t) (H : AreLinks types) : Link types.(Synthetic) :=
      H.(H_Synthetic _).
    Global Instance IsLinkSynthetic1 (types : t) (H : AreLinks types) : Link types.(Synthetic1) :=
      H.(H_Synthetic1 _).
    Global Instance IsLinkSynthetic2 (types : t) (H : AreLinks types) : Link types.(Synthetic2) :=
      H.(H_Synthetic2 _).
  End AssociatedTypes.

  Definition Run_width
      (Self T : Set) `{Link Self} `{Link T} :
      Set :=
    TraitMethod.C (trait Self T) "width" (fun method =>
      forall
        (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Usize.t
    ).

  Definition Run_height
      (Self T : Set) `{Link Self} `{Link T} :
      Set :=
    TraitMethod.C (trait Self T) "height" (fun method =>
      forall
        (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Usize.t
    ).

  Definition Run_dimensions
      (Self T : Set) `{Link Self} `{Link T} :
      Set :=
    TraitMethod.C (trait Self T) "dimensions" (fun method =>
      forall
        (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Dimensions.t
    ).

  Definition Run_get
      (Self T : Set) `{Link Self} `{Link T} :
      Set :=
    TraitMethod.C (trait Self T) "get" (fun method =>
      forall
        (self : Ref.t Pointer.Kind.Ref Self)
        (r c : Usize.t),
      Run.Trait method [] [] [ φ self; φ r; φ c ] T
    ).

  Definition Run_row
      (Self T : Set) `{Link Self} `{Link T}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self T) "row" (fun method =>
      forall
        (self : Ref.t Pointer.Kind.Ref Self)
        (r : Usize.t),
      Run.Trait method [] [] [ φ self; φ r ] types.(AssociatedTypes.Row)
    ).

  Definition Run_rows
      (Self T : Set) `{Link Self} `{Link T}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self T) "rows" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] types.(AssociatedTypes.Synthetic)
    ).

  Definition Run_par_rows
      (Self T : Set) `{Link Self} `{Link T}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self T) "par_rows" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] types.(AssociatedTypes.Synthetic1)
    ).

  Definition Run_row_slice
      (Self T : Set) `{Link Self} `{Link T}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self T) "row_slice" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (r : Usize.t),
      Run.Trait method [] [] [ φ self; φ r ] types.(AssociatedTypes.Synthetic2)
    ).

  Class Run
      (Self T : Set) `{Link Self} `{Link T}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set := {
    Row_IsAssociated :
      IsTraitAssociatedType "p3_matrix::Matrix" [] [Φ T] (Φ Self)
      "Row" (Φ types.(AssociatedTypes.Row));
    Synthetic_IsAssociated :
      IsTraitAssociatedType "p3_matrix::Matrix" [] [Φ T] (Φ Self)
      "{{synthetic}}" (Φ types.(AssociatedTypes.Synthetic));
    Synthetic1_IsAssociated :
      IsTraitAssociatedType "p3_matrix::Matrix" [] [Φ T] (Φ Self)
      "{{synthetic}}'1" (Φ types.(AssociatedTypes.Synthetic1));
    Synthetic2_IsAssociated :
      IsTraitAssociatedType "p3_matrix::Matrix" [] [Φ T] (Φ Self)
      "{{synthetic}}'2" (Φ types.(AssociatedTypes.Synthetic2));
    run_Deref_for_Synthetic2 :
      Deref.Run types.(AssociatedTypes.Synthetic2) (list T);
    width : Run_width Self T;
    height : Run_height Self T;
    dimensions : Run_dimensions Self T;
    get : Run_get Self T;
    row : Run_row Self T types;
    rows : Run_rows Self T types;
    par_rows : Run_par_rows Self T types;
    row_slice : Run_row_slice Self T types;
  }.
End Matrix.
