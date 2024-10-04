Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.move_sui.simulations.mutual.lib.
Require Import Coq.Lists.List.

Import simulations.M.Notations.

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
  (* Admitted:
   * Definition new (code : list Bytecode.t) : VMControlFlowGraph.t. Admitted.
   *)

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

  Definition record_block_ids (pc : CodeOffset.t)
                            (code : list Bytecode.t)
                            (block_ids : Set_.t BlockId.t) : Set_.t BlockId.t :=
  match List.nth_error code (Z.to_nat pc) with
  | Some bytecode =>
    let block_ids :=
      match Bytecode.offset bytecode with
      | Some offset => Set_.add offset block_ids
      | None => block_ids
      end in
    if andb (Bytecode.is_branch bytecode) ((pc + 1) <? Z.of_nat (length code)) then
      Set_.add (pc + 1)%Z block_ids
    else
      block_ids
  | None => block_ids
  end.

    

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
