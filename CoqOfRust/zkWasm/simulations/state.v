Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.

Require Import zkWasm.circuits.etable.simulations.allocator_type.
Require Import zkWasm.circuits.etable.simulations.constraint_builder.

Import simulations.M.Notations.

Module State.
  (*
    allocator: &mut EventTableCellAllocator<F>,
    constraint_builder: &mut ConstraintBuilder<F>,
  *)
  Record t {F : Set} {H : deps.FieldExt.Trait F} : Set := {
    allocator : EventTableCellAllocator.t F;
    constraint_builder : ConstraintBuilder.t F;
  }.
  Arguments t _ {_}.

  Module Lens.
    Definition allocator {F : Set} {_ : deps.FieldExt.Trait F} :
        Lens.t (t F) (EventTableCellAllocator.t F) := {|
      Lens.read st := st.(allocator);
      Lens.write st v := st <| allocator := v |>;
    |}.

    Definition constraint_builder {F : Set} {_ : deps.FieldExt.Trait F} :
        Lens.t (t F) (ConstraintBuilder.t F) := {|
      Lens.read st := st.(constraint_builder);
      Lens.write st v := st <| constraint_builder := v |>;
    |}.
  End Lens.
End State.
