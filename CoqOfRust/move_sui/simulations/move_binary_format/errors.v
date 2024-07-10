Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

Require CoqOfRust.move_sui.simulations.move_binary_format.file_format.
Module TableIndex := file_format.TableIndex.

(* TODO(progress):
- Plan: much more details should be irrevalent, so we only do 
  a simple wrap up here as lazy as possibles
- Make a stub for `StatusCode`
- Make a stub for `ExecutionState`
- Find `IndexKind`, `TableIndex`, `FunctionDefinitionIndex` and `CodeOffset`
*)

(* 
#[derive(Clone)]
pub struct PartialVMError(Box<PartialVMError_>);

#[derive(Clone)]
struct PartialVMError_ {
    major_status: StatusCode,
    sub_status: Option<u64>,
    message: Option<String>,
    exec_state: Option<ExecutionState>,
    indices: Vec<(IndexKind, TableIndex)>,
    offsets: Vec<(FunctionDefinitionIndex, CodeOffset)>,
}
*)
Module PartialVMError_.
  Record t : Set := {
  (* TODO: Implement below *)
    (* major_status: StatusCode; *)
    sub_status : option Z;
    message: option string;
    (* exec_state: Option<ExecutionState>; *)
    (* indices: Vec<(IndexKind, TableIndex)>; *)
    (* offsets: Vec<(FunctionDefinitionIndex, CodeOffset)>; *)
 
  }.
End PartialVMError_.

Module PartialVMError.
  Record t : Set := {
    _ : PartialVMError_.t;
  }.
End PartialVMError.

(* pub type PartialVMResult<T> = ::std::result::Result<T, PartialVMError>; *)
Module PartialVMResult.
  Definition t (T : Set) := Result.t T PartialVMError.t.
  (* 
  impl PartialVMError {
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

      pub fn at_code_offset(mut self, function: FunctionDefinitionIndex, offset: CodeOffset) -> Self {
          self.0.offsets.push((function, offset));
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
  Module Impl_move_sui_simulations_move_binary_format_error_PartialVMResult.
    (* TODO: Implement `new` function *)
    Definition new : Set. Admitted.

    (* TODO: Implement at_code_offset *)
  End Impl_move_sui_simulations_move_binary_format_error_PartialVMResult.
End PartialVMResult.
