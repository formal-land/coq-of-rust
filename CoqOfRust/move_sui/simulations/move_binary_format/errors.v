Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

Require CoqOfRust.move_sui.simulations.move_binary_format.lib.
Module IndexKind := move_binary_format.lib.IndexKind.

(* TODO(progress):
  - Rewrite `mut` functions with `StatePanic` monads, for example `at_code_offset`. 
    Maybe implement Lens for `PartialVMError`. See the NOTE there
*)

Require CoqOfRust.move_sui.simulations.move_binary_format.file_format.
Module TableIndex := file_format.TableIndex.
Module FunctionDefinitionIndex := file_format.FunctionDefinitionIndex.
Module CodeOffset := file_format.CodeOffset.

Require CoqOfRust.move_sui.simulations.move_core_types.vm_status.
Module StatusCode := vm_status.StatusCode.

(* NOTE: STUB: Implement this only if necessary *)
Module ExecutionState.
  Inductive t : Set := .
End ExecutionState.

Module Location.
  Inductive t : Set :=
  | Undefined
  (* | Module _ : (* language_storage::ModuleId *) *)
  .
End Location.

(** We merge [VMError] and [VMError_]. *)
Module VMError.
  Record t : Set := {
    major_status  : StatusCode.t;
    sub_status    : option Z;
    message       : option string;
    exec_state    : option ExecutionState.t;
    location      : Location.t;
    indices       : list (IndexKind.t * TableIndex.t);
    offsets       : list (FunctionDefinitionIndex.t * CodeOffset.t);
  }.
End VMError.

(** We merge [PartialVMError] and [PartialVMError_]. *)
Module PartialVMError.
  Record t : Set := {
    major_status  : StatusCode.t;
    sub_status    : option Z;
    message       : option string;
    exec_state    : option ExecutionState.t;
    indices       : list (IndexKind.t * TableIndex.t);
    offsets       : list (FunctionDefinitionIndex.t * CodeOffset.t);
  }.

  (* 
  impl PartialVMError {
      pub fn finish(self, location: Location) -> VMError {
          let PartialVMError_ {
              major_status,
              sub_status,
              message,
              exec_state,
              indices,
              offsets,
          } = *self.0;
          VMError(Box::new(VMError_ {
              major_status,
              sub_status,
              message,
              exec_state,
              location,
              indices,
              offsets,
          }))
      }

      pub fn major_status(&self) -> StatusCode {
          self.0.major_status
      }

      pub fn with_sub_status(mut self, sub_status: u64) -> Self {
          debug_assert!(self.0.sub_status.is_none());
          self.0.sub_status = Some(sub_status);
          self
      }

      pub fn with_message(mut self, message: String) -> Self {
          debug_assert!(self.0.message.is_none());
          self.0.message = Some(message);
          self
      }

      pub fn with_exec_state(mut self, exec_state: ExecutionState) -> Self {
          debug_assert!(self.0.exec_state.is_none());
          self.0.exec_state = Some(exec_state);
          self
      }

      pub fn at_index(mut self, kind: IndexKind, index: TableIndex) -> Self {
          self.0.indices.push((kind, index));
          self
      }

      pub fn at_indices(mut self, additional_indices: Vec<(IndexKind, TableIndex)>) -> Self {
          self.0.indices.extend(additional_indices);
          self
      }

      pub fn at_code_offsets(
          mut self,
          additional_offsets: Vec<(FunctionDefinitionIndex, CodeOffset)>,
      ) -> Self {
          self.0.offsets.extend(additional_offsets);
          self
      }

      /// Append the message `message` to the message field of the VM status, and insert a seperator
      /// if the original message is non-empty.
      pub fn append_message_with_separator(
          mut self,
          separator: char,
          additional_message: String,
      ) -> Self {
          match self.0.message.as_mut() {
              Some(msg) => {
                  if !msg.is_empty() {
                      msg.push(separator);
                  }
                  msg.push_str(&additional_message);
              }
              None => self.0.message = Some(additional_message),
          };
          self
      }
  }
  *)

  (* 
  pub fn all_data(
      self,
  ) -> (
      StatusCode,
      Option<u64>,
      Option<String>,
      Option<ExecutionState>,
      Vec<(IndexKind, TableIndex)>,
      Vec<(FunctionDefinitionIndex, CodeOffset)>,
  ) {
      let PartialVMError_ {
          major_status,
          sub_status,
          message,
          exec_state,
          indices,
          offsets,
      } = *self.0;
      (
          major_status,
          sub_status,
          message,
          exec_state,
          indices,
          offsets,
      )
  }
  *)
  Definition all_data (self : t) :
      StatusCode.t *
      option Z *
      option string *
      option ExecutionState.t *
      list (IndexKind.t * TableIndex.t) *
      list (FunctionDefinitionIndex.t * CodeOffset.t) :=
  (
    self.(major_status),
    self.(sub_status),
    self.(message),
    self.(exec_state),
    self.(indices),
    self.(offsets)
  ).

  (* 
  pub fn new(major_status: StatusCode) -> Self {
      Self(Box::new(PartialVMError_ {
          major_status,
          sub_status: None,
          message: None,
          exec_state: None,
          indices: vec![],
          offsets: vec![],
      }))
  }
  *)
  Definition new (major_status : StatusCode.t) : t :=
    {|
      major_status  := major_status;
      sub_status    := None;
      message       := None;
      exec_state    := None;
      indices       := [];
      offsets       := [];
    |}.

  (*
  pub fn at_code_offset(mut self, function: FunctionDefinitionIndex, offset: CodeOffset) -> Self {
      self.0.offsets.push((function, offset));
      self
  }
  *)
  Definition at_code_offset
      (self : t)
      (function : FunctionDefinitionIndex.t) 
      (offset : CodeOffset.t) :
      t :=
    self <| offsets := (function, offset) :: self.(offsets) |>.
End PartialVMError.

(* pub type PartialVMResult<T> = ::std::result::Result<T, PartialVMError>; *)
Module PartialVMResult.
  Definition t (T : Set) := Result.t T PartialVMError.t.
End PartialVMResult.
