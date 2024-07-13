Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

Require CoqOfRust.move_sui.simulations.move_binary_format.lib.
Module IndexKind := move_binary_format.lib.IndexKind.

(* TODO: Mutual Dependency issue. To be solved in some way *)
Require CoqOfRust.move_sui.simulations.move_binary_format.file_format.
Module TableIndex := file_format.TableIndex.
Module FunctionDefinitionIndex := file_format.FunctionDefinitionIndex.
Module CodeOffset := file_format.CodeOffset.

Require CoqOfRust.move_sui.simulations.move_core_types.vm_status.
Module StatusCode := vm_status.StatusCode.

(* NOTE: Implement this only if necessary *)
Module ExecutionState.
  Inductive t : Set := .
End ExecutionState.

(* TODO(progress): 
- Implement `new` and figure out a way to make the constructor
*)

Module PartialVMError_.
  Record t : Set := {
    major_status: StatusCode.t;
    sub_status : option Z;
    message: option string;
    exec_state: option ExecutionState.t;
    indices: list (IndexKind.t * TableIndex.t);
    offsets: list (FunctionDefinitionIndex.t * CodeOffset.t);
  }.
End PartialVMError_.

Module PartialVMError.
  Record t : Set := {
    _ : PartialVMError_.t;
  }.
End PartialVMError.

Definition t (T : Set) := Result.t T PartialVMError.t.
Print t.

(* pub type PartialVMResult<T> = ::std::result::Result<T, PartialVMError>; *)
Module PartialVMResult.
  Definition t (T : Set) := Result.t T PartialVMError.t.
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
  Module Impl_move_sui_simulations_move_binary_format_errors_PartialVMResult.
    Definition Self := move_sui.simulations.move_binary_format.errors.PartialVMResult.t.
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
    Definition all_data (self : Self) :
      (StatusCode.t * (option Z) * (option string) * (option ExecutionState.t) 
        * (list (IndexKind.t * TableIndex.t)) * (list (FunctionDefinitionIndex.t * CodeOffset.t))).
    Admitted.

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
    Definition new (self : Self) (major_status : StatusCode.t) : Self. Admitted.
    (* 
    let pvme_ := {|
    
    |} in
    let pvme := PartialVMError.Build_t pvme_ in
    (* ??? *)
    *)

    (*
    pub fn at_code_offset(mut self, function: FunctionDefinitionIndex, offset: CodeOffset) -> Self {
        self.0.offsets.push((function, offset));
        self
    }
    *)
    Definition at_code_offset (self : Self) : Set. Admitted.
  End Impl_move_sui_simulations_move_binary_format_errors_PartialVMResult.
End PartialVMResult.
