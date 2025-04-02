Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.iter.traits.collect.
Require Import core.iter.traits.links.iterator.

(*
pub trait IntoIterator {
    type Item;
    type IntoIter: Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter;
}
*)
Module IntoIterator.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("core::iter::traits::collect::IntoIterator", [], [], Φ Self).

  Module Types.
    Record t : Type := {
      Item : Set;
      IntoIter : Set;
    }.

    Class AreLinks (types : t) : Set := {
      H_Item : Link types.(Item);
      H_IntoIter : Link types.(IntoIter);
    }.

    Global Instance IsLinkItem (types : t) (H : AreLinks types) : Link types.(Item) :=
      H.(H_Item _).
    Global Instance IsLinkIntoIter (types : t) (H : AreLinks types) : Link types.(IntoIter) :=
      H.(H_IntoIter _).
  End Types.

  Definition Run_into_iter
      (Self : Set) `{Link Self}
      (types : Types.t) `{Types.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "into_iter" (fun method =>
      forall (self : Self),
      Run.Trait method [] [] [φ self] types.(Types.IntoIter)
    ).

  Class Run
      (Self : Set) `{Link Self}
      (types : Types.t) `{Types.AreLinks types} :
      Set := {
    Item_IsAssociated :
      IsTraitAssociatedType
        "core::iter::traits::collect::IntoIterator" [] [] (Φ Self)
        "Item" (Φ types.(Types.Item));
    IntoIter_IsAssociated :
      IsTraitAssociatedType
        "core::iter::traits::collect::IntoIterator" [] [] (Φ Self)
        "IntoIter" (Φ types.(Types.IntoIter));
    run_Iterator_for_IntoIter : Iterator.Run types.(Types.IntoIter) types.(Types.Item);
    run_into_iter : Run_into_iter Self types;
  }.
End IntoIterator.

(* impl<I: Iterator> IntoIterator for I *)
Module Impl_IntoIterator_for_Iterator_I.
  Definition Self (I : Set) `{Link I} : Set :=
    I.

  (*
    type Item = I::Item;
    type IntoIter = I;
  *)
  Definition types
    (I : Set) `{Link I}
    (Item : Set) `{Link Item} :
    IntoIterator.Types.t :=
  {|
    IntoIterator.Types.Item := Item;
    IntoIterator.Types.IntoIter := Self I;
  |}.

  Global Instance types_AreLinks
    (I : Set) `{Link I}
    (Item : Set) `{Link Item} :
    IntoIterator.Types.AreLinks (types I Item).
  Proof.
    now constructor.
  Defined.

  Definition run_into_iter
    (I : Set) `{Link I}
    (Item : Set) `{Link Item} :
    IntoIterator.Run_into_iter (Self I) (types I Item).
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply iter.traits.collect.Impl_core_iter_traits_collect_IntoIterator_where_core_iter_traits_iterator_Iterator_I_for_I.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
    }
  Defined.

  Instance run
    (I : Set) `{Link I}
    (Item : Set) `{Link Item} :
    IntoIterator.Run (Self I) (types I Item).
  Proof.
  Admitted.
End Impl_IntoIterator_for_Iterator_I.
