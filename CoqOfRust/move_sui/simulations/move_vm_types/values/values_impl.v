Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

Require CoqOfRust.move_sui.simulations.move_binary_format.errors.
Module PartialVMResult := errors.PartialVMResult.
Module PartialVMError := errors.PartialVMError.

Require CoqOfRust.move_sui.simulations.move_core_types.vm_status.
Module StatusCode := vm_status.StatusCode.

(* TODO(progress): 
- Implement `Locals`
*)

(* NOTE(STUB): Only implement if necessary *)
Module Locals.
  Parameter t : Set.
End Locals.

Module AccountAddress.
  Parameter t : Set.
End AccountAddress.

Module Container.
  Parameter t : Set.
End Container.

Module ContainerRef.
  Parameter t : Set.
End ContainerRef.

Module IndexedRef.
  Parameter t : Set.
End IndexedRef.

(* **************** *)

(* 
enum ValueImpl {
    Invalid,

    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    U256(u256::U256),
    Bool(bool),
    Address(AccountAddress),

    Container(Container),

    ContainerRef(ContainerRef),
    IndexedRef(IndexedRef),
}
*)
Module ValueImpl.
  Inductive t : Set :=
  | Invalid
  | U8 : Z -> t
  | U16 : Z -> t
  | U32 : Z -> t
  | U64 : Z -> t
  | U128 : Z -> t
  | U256 : Z -> t
  | Bool : bool -> t
  | Address : AccountAddress.t -> t
  | Container : Container.t -> t
  | ContainerRef : ContainerRef.t -> t
  | IndexedRef : IndexedRef.t -> t
  .
End ValueImpl.

(* pub struct Value(ValueImpl); *)
Module Value.
  Definition t : Set := ValueImpl.t.

  (* 
  NOTE: We just roughly implement it as a collection of functions since it's also performance-wise nice. 
    Otherwise, this might be helpful: 
    https://stackoverflow.com/questions/70946233/coq-obtaining-equality-from-match-statement

  macro_rules! impl_vm_value_cast {
      ($ty: ty, $tc: ident) => {
          impl VMValueCast<$ty> for Value {
              fn cast(self) -> PartialVMResult<$ty> {
                  match self.0 {
                      ValueImpl::$tc(x) => Ok(x),
                      v => Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
                          .with_message(format!("cannot cast {:?} to {}", v, stringify!($ty)))),
                  }
              }
          }
      };
  }

  impl_vm_value_cast!(u8, U8);
  impl_vm_value_cast!(u16, U16);
  impl_vm_value_cast!(u32, U32);
  impl_vm_value_cast!(u64, U64);
  impl_vm_value_cast!(u128, U128);
  impl_vm_value_cast!(u256::U256, U256);
  impl_vm_value_cast!(bool, Bool);
  impl_vm_value_cast!(AccountAddress, Address);
  impl_vm_value_cast!(ContainerRef, ContainerRef);
  impl_vm_value_cast!(IndexedRef, IndexedRef);
  *)
  Module cast.
    Definition cast_u8 (self : t) : PartialVMResult.t Z := 
      match self with
      | ValueImpl.U8 x => Result.Ok x
      | _ => Result.Err $ PartialVMError.Impl_PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
      end.

    Definition cast_u16 (self : t) : PartialVMResult.t Z := 
      match self with
      | ValueImpl.U16 x => Result.Ok x
      | _ => Result.Err $ PartialVMError.Impl_PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
      end.

    Definition cast_u32 (self : t) : PartialVMResult.t Z := 
      match self with
      | ValueImpl.U32 x => Result.Ok x
      | _ => Result.Err $ PartialVMError.Impl_PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
      end.

    Definition cast_u64 (self : t) : PartialVMResult.t Z := 
      match self with
      | ValueImpl.U64 x => Result.Ok x
      | _ => Result.Err $ PartialVMError.Impl_PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
      end.

    Definition cast_u128 (self : t) : PartialVMResult.t Z := 
      match self with
      | ValueImpl.U128 x => Result.Ok x
      | _ => Result.Err $ PartialVMError.Impl_PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
      end.

    Definition cast_u256 (self : t) : PartialVMResult.t Z := 
      match self with
      | ValueImpl.U256 x => Result.Ok x
      | _ => Result.Err $ PartialVMError.Impl_PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
      end.

    Definition cast_bool (self : t) : PartialVMResult.t bool := 
      match self with
      | ValueImpl.Bool x => Result.Ok x
      | _ => Result.Err $ PartialVMError.Impl_PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
      end.

    Definition cast_AccountAddress (self : t) : PartialVMResult.t AccountAddress.t := 
      match self with
      | ValueImpl.Address x => Result.Ok x
      | _ => Result.Err $ PartialVMError.Impl_PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
      end.

    Definition cast_ContainerRef (self : t) : PartialVMResult.t ContainerRef.t := 
      match self with
      | ValueImpl.ContainerRef x => Result.Ok x
      | _ => Result.Err $ PartialVMError.Impl_PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
      end.

    Definition cast_IndexedRef (self : t) : PartialVMResult.t IndexedRef.t := 
      match self with
      | ValueImpl.IndexedRef x => Result.Ok x
      | _ => Result.Err $ PartialVMError.Impl_PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
      end.
  End cast.

  Module Impl_Value.
    (* 
    fn constant_sig_token_to_layout(constant_signature: &SignatureToken) -> Option<MoveTypeLayout> {
        use MoveTypeLayout as L;
        use SignatureToken as S;

        Some(match constant_signature {
            S::Bool => L::Bool,
            S::U8 => L::U8,
            S::U16 => L::U16,
            S::U32 => L::U32,
            S::U64 => L::U64,
            S::U128 => L::U128,
            S::U256 => L::U256,
            S::Address => L::Address,
            S::Signer => return None,
            S::Vector(inner) => L::Vector(Box::new(Self::constant_sig_token_to_layout(inner)?)),
            // Not yet supported
            S::Struct(_) | S::StructInstantiation(_) => return None,
            // Not allowed/Not meaningful
            S::TypeParameter(_) | S::Reference(_) | S::MutableReference(_) => return None,
        })
    }

    pub fn deserialize_constant(constant: &Constant) -> Option<Value> {
        let layout = Self::constant_sig_token_to_layout(&constant.type_)?;
        Value::simple_deserialize(&constant.data, &layout)
    }
    *)
  End Impl_Value.
End Value.
