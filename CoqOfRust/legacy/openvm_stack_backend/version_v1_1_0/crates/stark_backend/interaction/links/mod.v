Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import openvm_stack_backend.version_v1_1_0.crates.stark_backend.interaction.mod.
Require Import plonky3.commit_539bbc84.air.links.air.

(* pub type BusIndex = u16; *)
Module BusIndex.
  Definition t : Set := U16.t.
End BusIndex.

(*
  pub trait InteractionBuilder: AirBuilder {
      fn push_interaction<E: Into<Self::Expr>>(
          &mut self,
          bus_index: BusIndex,
          fields: impl IntoIterator<Item = E>,
          count: impl Into<Self::Expr>,
          count_weight: u32,
      );
      fn num_interactions(&self) -> usize;
      fn all_interactions(&self) -> &[Interaction<Self::Expr>];
  }
*)
Module InteractionBuilder.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("openvm_stack_backend::stark_backend::interaction::InteractionBuilder", [], [], Φ Self).

  (* TODO: make more precise *)
  (* Definition Run_push_interaction
      (Self E : Set) `{Link Self} `{Link E}
      (types : AirBuilder.AssociatedTypes.t) `{AirBuilder.AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "push_interaction" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [] [ φ self ] types.(AirBuilder.AssociatedTypes.Expr)
    ). *)

  Class Run
    (Self : Set) `{Link Self}
    (types : AirBuilder.AssociatedTypes.t) `{AirBuilder.AssociatedTypes.AreLinks types} :
    Set := {
    run_AirBuilder_for_Self : AirBuilder.Run Self types;
  }.
End InteractionBuilder.
