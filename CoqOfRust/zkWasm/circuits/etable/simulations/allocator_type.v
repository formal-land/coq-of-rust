Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.

Require zkWasm.circuits.simulations.cell.
Require zkWasm.simulations.deps.

Import simulations.M.Notations.

Module AllocatedMemoryTableLookupReadCell.
  Parameter t : forall (F : Set) {_ : deps.FieldExt.Trait F}, Set.
End AllocatedMemoryTableLookupReadCell.

Module AllocatedMemoryTableLookupWriteCell.
  Parameter t : forall (F : Set) {_ : deps.FieldExt.Trait F}, Set.
End AllocatedMemoryTableLookupWriteCell.

(* pub(crate) struct EventTableCellAllocator<F: FieldExt> {
    k: u32,
    pub(crate) free_cells: BTreeMap<EventTableCellType, (usize, u32)>,
    all_cols: BTreeMap<EventTableCellType, Vec<Vec<Column<Advice>>>>,
    free_u32_cells: Vec<AllocatedU32Cell<F>>,
    free_u32_permutation_cells: Vec<AllocatedU32PermutationCell<F>>,
    free_u64_cells: Vec<AllocatedU64Cell<F>>,
    _mark: PhantomData<F>,
} *)
Module EventTableCellAllocator.
  Parameter t : forall (F : Set) {_ : deps.FieldExt.Trait F}, Set.
End EventTableCellAllocator.
