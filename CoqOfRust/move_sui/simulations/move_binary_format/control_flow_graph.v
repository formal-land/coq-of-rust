Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require CoqOfRust.core.simulations.assert.
Require Import CoqOfRust.move_sui.simulations.mutual.lib.

Import simulations.M.Notations.
Import assert.Notations.

Require CoqOfRust.move_sui.simulations.move_binary_format.file_format.
Module Bytecode := file_format.Bytecode.
Module CodeOffset := file_format.CodeOffset.

(* pub type BlockId = CodeOffset; *)
Module BlockId.
  Definition t : Set := CodeOffset.t.
End BlockId.

(*
const ENTRY_BLOCK_ID: BlockId = 0;
*)
Definition ENTRY_BLOCK_ID : BlockId.t := 0.

(* pub trait ControlFlowGraph { *)
(* We do not implement this trait as it is used only once. *)

(*
struct BasicBlock {
    exit: CodeOffset,
    successors: Vec<BlockId>,
}
*)
Module BasicBlock.
  Record t : Set := {
    exit : CodeOffset.t;
    successors : list BlockId.t;
  }.
End BasicBlock.

(* 
pub struct VMControlFlowGraph {
    /// The basic blocks
    blocks: Map<BlockId, BasicBlock>,
    /// Basic block ordering for traversal
    traversal_successors: Map<BlockId, BlockId>,
    /// Map of loop heads with all of their back edges
    loop_heads: Map<BlockId, /* back edges */ Set<BlockId>>,
}
*)
(* NOTE: STUB: only implement if necessary *)
Module VMControlFlowGraph.
  Record t : Set := {
    blocks : Map.t BlockId.t BasicBlock.t;
    traversal_successors : Map.t BlockId.t BlockId.t;
    loop_heads : Map.t BlockId.t (Set_.t BlockId.t);
  }.
End VMControlFlowGraph.

Module Impl_VMControlFlowGraph.
  (*
  fn record_block_ids(pc: CodeOffset, code: &[Bytecode], block_ids: &mut Set<BlockId>) {
      let bytecode = &code[pc as usize];

      if let Some(offset) = bytecode.offset() {
          block_ids.insert(*offset); (* Dereferencing syntax *)*)
      }

      if bytecode.is_branch() && pc + 1 < (code.len() as CodeOffset) {
          block_ids.insert(pc + 1);
      }
  }
  *)
  Definition record_block_ids
      (pc : CodeOffset.t)
      (code : list Bytecode.t)
      (block_ids : Set_.t BlockId.t) :
      Set_.t BlockId.t :=
    match List.nth_error code (Z.to_nat pc) with
    | Some bytecode =>
      let block_ids :=
        match Bytecode.offset bytecode with
        | Some offset => Set_.add offset block_ids
        | None => block_ids
        end in
      if andb (Bytecode.is_branch bytecode) ((pc + 1) <? Z.of_nat (List.length code)) then
        Set_.add (pc + 1)%Z block_ids
      else
        block_ids
    | None => block_ids
    end.

  (*
  fn is_end_of_block(pc: CodeOffset, code: &[Bytecode], block_ids: &Set<BlockId>) -> bool {
      pc + 1 == (code.len() as CodeOffset) || block_ids.contains(&(pc + 1))
  }
  *)
  Definition is_end_of_block
      (pc : CodeOffset.t)
      (code : list Bytecode.t)
      (block_ids : Set_.t BlockId.t) :
      bool :=
    ((pc + 1) =? Z.of_nat (List.length code)) ||
    (Set_.mem (pc + 1)%Z block_ids).

  (*
  #[derive(Copy, Clone)]
  enum Exploration {
      InProgress,
      Done,
  }
  *)
  Module Exploration.
    Inductive t : Set :=
    | InProgress
    | Done.
  End Exploration.

  Axiom new_traversal_successors : list Bytecode.t -> Map.t BlockId.t BlockId.t.
  Axiom new_loop_heads : list Bytecode.t -> Map.t BlockId.t (Set_.t BlockId.t).

  Definition new (code : list Bytecode.t) : M! VMControlFlowGraph.t :=
    (* let code_len = code.len() as CodeOffset; *)
    let code_len := Z.of_nat (List.length code) in
    (*
    let mut block_ids = Set::new();
    block_ids.insert(ENTRY_BLOCK_ID);
    for pc in 0..code.len() {
        VMControlFlowGraph::record_block_ids(pc as CodeOffset, code, &mut block_ids);
    }
    *)
    let block_ids := Set_.empty in
    let block_ids := Set_.add ENTRY_BLOCK_ID block_ids in
    let block_ids := List.fold_left (fun block_ids pc =>
      record_block_ids (Z.of_nat pc) code block_ids
    ) (List.seq 0 (Z.to_nat code_len)) block_ids in
    (*
    let mut blocks = Map::new();
    let mut entry = 0;
    let mut exit_to_entry = Map::new();
    for pc in 0..code.len() {
        let co_pc = pc as CodeOffset;

        // Create a basic block
        if Self::is_end_of_block(co_pc, code, &block_ids) {
            let exit = co_pc;
            exit_to_entry.insert(exit, entry);
            let successors = Bytecode::get_successors(co_pc, code);
            let bb = BasicBlock { exit, successors };
            blocks.insert(entry, bb);
            entry = co_pc + 1;
        }
    }
    *)
    let blocks := Map.empty in
    let entry := 0 in
    let! (blocks, entry) :=
      Panic.fold_left
        (blocks, entry)
        (List.seq 0 (Z.to_nat code_len))
        (fun '(blocks, entry) pc =>
          let co_pc := Z.of_nat pc in
          if is_end_of_block co_pc code block_ids then
            let exit := co_pc in
            let! successors := Bytecode.get_successors co_pc code in
            let bb := {|
              BasicBlock.exit := exit;
              BasicBlock.successors := successors
            |} in
            let blocks := Map.add entry bb blocks in
            let entry := (co_pc + 1)%Z in
            return! (blocks, entry)
          else
            return! (blocks, entry)
        ) in
    (*
    let blocks = blocks;
    assert_eq!(entry, code_len);
    *)
    let! _ := assert_eq! entry code_len in
    (* TODO: complete the code with the fields that are axiom for now. *)
    return! {|
      VMControlFlowGraph.blocks := blocks;
      VMControlFlowGraph.traversal_successors := new_traversal_successors code;
      VMControlFlowGraph.loop_heads := new_loop_heads code;
    |}.

  (*
   * Beginning of the `new` function:
   *)

  Definition code_len (code : list Bytecode.t) : CodeOffset.t :=
    Z.of_nat (List.length code).

  (*
  Definition new (code : list Bytecode.t) : VMControlFlowGraph.t :=
    let code_length := code_len code in
    let block_ids := BlockIdSet.add ENTRY_BLOCK_ID BlockIdSet.empty in
  (* TO BE CONTINUED *)
  *)

  (* We put here the functions from the trait [ControlFlowGraph] as it is used only once. *)
  (*
    fn block_start(&self, block_id: BlockId) -> CodeOffset {
        block_id
    }
  *)
  Definition block_start (self : VMControlFlowGraph.t) (block_id : BlockId.t) : CodeOffset.t :=
    block_id.

  (*
    fn block_end(&self, block_id: BlockId) -> CodeOffset {
        self.blocks[&block_id].exit
    }
  *)
  Definition block_end (self : VMControlFlowGraph.t) (block_id : BlockId.t) : CodeOffset.t :=
    match Map.get self.(VMControlFlowGraph.blocks) block_id with
    | Some block => block.(BasicBlock.exit)
    | None => 0 (* NOTE: unreachable code *)
    end.

  (*
    fn instr_indexes(&self, block_id: BlockId) -> Box<dyn Iterator<Item = CodeOffset>> {
        Box::new(self.block_start(block_id)..=self.block_end(block_id))
    }
  *)
  Definition instr_indexes (self : VMControlFlowGraph.t) (block_id : BlockId.t) :
      list CodeOffset.t :=
    let start := block_start self block_id in
    let end_ := block_end self block_id in
    let length := (end_ - start + 1)%Z in
    List.map Z.of_nat $ List.seq (Z.to_nat start) (Z.to_nat length).

  (*
    fn blocks(&self) -> Vec<BlockId> {
        self.blocks.keys().cloned().collect()
    }
  *)
  Definition blocks (self : VMControlFlowGraph.t) : list BlockId.t :=
    Map.keys (VMControlFlowGraph.blocks self).
End Impl_VMControlFlowGraph.
