Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.

Require Import zkWasm.circuits.etable.simulations.allocator_type.
Require Import zkWasm.circuits.simulations.cell.
Require Import zkWasm.simulations.deps.
Require Import zkWasm.simulations.state.

Import simulations.M.Notations.

(* impl<F: FieldExt> EventTableCellAllocator<F> { *)
Module Impl_EventTableCellAllocator.
  (* pub(crate) fn alloc_bit_cell(&mut self) -> AllocatedBitCell<F> {
        AllocatedBitCell {
            cell: self.alloc(&EventTableCellType::Bit),
        }
    } *)
  Definition alloc_bit_cell {F : Set} {_ : deps.FieldExt.Trait F} :
    MS? (State.t F) Empty_set (cell.AllocatedBitCell.t F).
  Admitted.

  (* pub(crate) fn alloc_u64_with_flag_bit_cell_dyn(
        &mut self,
        constraint_builder: &mut ConstraintBuilder<F>,
        is_i32: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + 'static,
    ) -> AllocatedU64CellWithFlagBitDyn<F> *)
  Definition alloc_u64_with_flag_bit_cell_dyn {F : Set} {_ : deps.FieldExt.Trait F}
    (is_i32 : unit) :
    MS? (State.t F) Empty_set (cell.AllocatedU64CellWithFlagBitDyn.t F).
  Admitted.
End Impl_EventTableCellAllocator.
