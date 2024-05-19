Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.

Require Import zkWasm.circuits.etable.simulations.allocator.
Require Import zkWasm.circuits.etable.simulations.allocator_type.
Require Import zkWasm.circuits.etable.simulations.constraint_builder.
Require Import zkWasm.circuits.etable.simulations.mod.
Require Import zkWasm.circuits.simulations.cell.
Require Import zkWasm.simulations.state.

Import simulations.M.Notations.

(* pub struct BinConfig<F: FieldExt> {
    lhs: AllocatedU64CellWithFlagBitDyn<F>,
    rhs: AllocatedU64CellWithFlagBitDyn<F>,

    is_i32: AllocatedBitCell<F>,

    d: AllocatedU64Cell<F>,
    d_flag_helper_diff: AllocatedCommonRangeCell<F>,

    aux1: AllocatedU64Cell<F>,
    aux2: AllocatedU64Cell<F>,

    overflow: AllocatedBitCell<F>,
    is_add: AllocatedBitCell<F>,
    is_sub: AllocatedBitCell<F>,
    is_mul: AllocatedBitCell<F>,
    is_div_u: AllocatedBitCell<F>,
    is_rem_u: AllocatedBitCell<F>,
    is_div_s: AllocatedBitCell<F>,
    is_rem_s: AllocatedBitCell<F>,
    is_div_s_or_rem_s: AllocatedBitCell<F>,

    res_flag: AllocatedUnlimitedCell<F>,
    size_modulus: AllocatedUnlimitedCell<F>,
    normalized_lhs: AllocatedUnlimitedCell<F>,
    normalized_rhs: AllocatedUnlimitedCell<F>,
    d_leading_u16: AllocatedUnlimitedCell<F>,
    degree_helper1: AllocatedUnlimitedCell<F>,
    degree_helper2: AllocatedUnlimitedCell<F>,

    memory_table_lookup_stack_read_lhs: AllocatedMemoryTableLookupReadCell<F>,
    memory_table_lookup_stack_read_rhs: AllocatedMemoryTableLookupReadCell<F>,
    memory_table_lookup_stack_write: AllocatedMemoryTableLookupWriteCell<F>,
} *)

Module BinConfig.
  Record t {F : Set} {H : deps.FieldExt.Trait F} : Set := {
    lhs : AllocatedU64CellWithFlagBitDyn.t F;
    rhs : AllocatedU64CellWithFlagBitDyn.t F;

    is_i32 : AllocatedBitCell.t F;

    d : AllocatedU64Cell.t F;
    d_flag_helper_diff : AllocatedCommonRangeCell.t F;

    aux1 : AllocatedU64Cell.t F;
    aux2 : AllocatedU64Cell.t F;

    overflow : AllocatedBitCell.t F;
    is_add : AllocatedBitCell.t F;
    is_sub : AllocatedBitCell.t F;
    is_mul : AllocatedBitCell.t F;
    is_div_u : AllocatedBitCell.t F;
    is_rem_u : AllocatedBitCell.t F;
    is_div_s : AllocatedBitCell.t F;
    is_rem_s : AllocatedBitCell.t F;
    is_div_s_or_rem_s : AllocatedBitCell.t F;

    res_flag : AllocatedUnlimitedCell.t F;
    size_modulus : AllocatedUnlimitedCell.t F;
    normalized_lhs : AllocatedUnlimitedCell.t F;
    normalized_rhs : AllocatedUnlimitedCell.t F;
    d_leading_u16 : AllocatedUnlimitedCell.t F;
    degree_helper1 : AllocatedUnlimitedCell.t F;
    degree_helper2 : AllocatedUnlimitedCell.t F;

    memory_table_lookup_stack_read_lhs : AllocatedMemoryTableLookupReadCell.t F;
    memory_table_lookup_stack_read_rhs : AllocatedMemoryTableLookupReadCell.t F;
    memory_table_lookup_stack_write : AllocatedMemoryTableLookupWriteCell.t F;
  }.
  Arguments t : clear implicits.
End BinConfig.

(* pub struct BinConfigBuilder {} *)

Module BinConfigBuilder.
  Inductive t : Set :=
  | Make.
End BinConfigBuilder.

Module Impl_EventTableOpcodeConfigBuilder_for_BinConfigBuilder.
  (* fn configure(
        common_config: &EventTableCommonConfig<F>,
        allocator: &mut EventTableCellAllocator<F>,
        constraint_builder: &mut ConstraintBuilder<F>,
    ) -> Box<dyn EventTableOpcodeConfig<F>> *)
  Definition configure {F : Set} {_ : deps.FieldExt.Trait F}
      (common_config : EventTableCommonConfig.t F) :
      MS? (State.t F) Empty_set unit.
    (*
      let is_i32 = allocator.alloc_bit_cell();
    *)
    refine (letS? is_i32 := Impl_EventTableCellAllocator.alloc_bit_cell in _).
    (*
      let lhs = allocator
            .alloc_u64_with_flag_bit_cell_dyn(constraint_builder, move |meta| is_i32.expr(meta));
    *)
    (* refine (letS? lhs :=
        (Impl_EventTableCellAllocator.alloc_u64_with_flag_bit_cell_dyn
          constraint_builder
          (fun meta => _)
        ) in _). *)
    refine (returnS? tt).
  Defined.
End Impl_EventTableOpcodeConfigBuilder_for_BinConfigBuilder.
