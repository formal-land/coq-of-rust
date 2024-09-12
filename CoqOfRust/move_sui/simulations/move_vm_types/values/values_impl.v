Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

Require CoqOfRust.move_sui.simulations.move_binary_format.errors.
Module PartialVMResult := errors.PartialVMResult.
Module PartialVMError := errors.PartialVMError.

Require CoqOfRust.move_sui.simulations.move_core_types.vm_status.
Module StatusCode := vm_status.StatusCode.

Require CoqOfRust.move_sui.simulations.move_binary_format.file_format.
Module SignatureToken.
  Include file_format.SignatureToken.
End SignatureToken.

(* TODO(progress): 
- Implement `Locals`
  - (FOCUS)Implement `move_loc`
  - Implement `store_loc`
  - Implement `borrow_loc`
*)

(* NOTE(STUB): Only implement if necessary *)
Module Constant.
  Parameter t : Set.
End Constant.

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
    #[derive(Clone)]
    struct SeedWrapper<L> {
        layout: L,
    }

    impl<'d> serde::de::DeserializeSeed<'d> for SeedWrapper<&MoveTypeLayout> {
        type Value = Value;

        fn deserialize<D: serde::de::Deserializer<'d>>(
            self,
            deserializer: D,
        ) -> Result<Self::Value, D::Error> {
            use MoveTypeLayout as L;

            match self.layout {
                L::Bool => bool::deserialize(deserializer).map(Value::bool),
                L::U8 => u8::deserialize(deserializer).map(Value::u8),
                L::U16 => u16::deserialize(deserializer).map(Value::u16),
                L::U32 => u32::deserialize(deserializer).map(Value::u32),
                L::U64 => u64::deserialize(deserializer).map(Value::u64),
                L::U128 => u128::deserialize(deserializer).map(Value::u128),
                L::U256 => u256::U256::deserialize(deserializer).map(Value::u256),
                L::Address => AccountAddress::deserialize(deserializer).map(Value::address),
                L::Signer => AccountAddress::deserialize(deserializer).map(Value::signer),

                L::Struct(struct_layout) => Ok(Value::struct_(
                    SeedWrapper {
                        layout: struct_layout,
                    }
                    .deserialize(deserializer)?,
                )),

                L::Vector(layout) => {
                    let container = match &**layout {
                        L::U8 => {
                            Container::VecU8(Rc::new(RefCell::new(Vec::deserialize(deserializer)?)))
                        }
                        L::U16 => {
                            Container::VecU16(Rc::new(RefCell::new(Vec::deserialize(deserializer)?)))
                        }
                        L::U32 => {
                            Container::VecU32(Rc::new(RefCell::new(Vec::deserialize(deserializer)?)))
                        }
                        L::U64 => {
                            Container::VecU64(Rc::new(RefCell::new(Vec::deserialize(deserializer)?)))
                        }
                        L::U128 => {
                            Container::VecU128(Rc::new(RefCell::new(Vec::deserialize(deserializer)?)))
                        }
                        L::U256 => {
                            Container::VecU256(Rc::new(RefCell::new(Vec::deserialize(deserializer)?)))
                        }
                        L::Bool => {
                            Container::VecBool(Rc::new(RefCell::new(Vec::deserialize(deserializer)?)))
                        }
                        L::Address => Container::VecAddress(Rc::new(RefCell::new(Vec::deserialize(
                            deserializer,
                        )?))),
                        layout => {
                            let v = deserializer
                                .deserialize_seq(VectorElementVisitor(SeedWrapper { layout }))?;
                            Container::Vec(Rc::new(RefCell::new(v)))
                        }
                    };
                    Ok(Value(ValueImpl::Container(container)))
                }
            }
        }
    }
    *)
    (* 
    pub fn simple_deserialize(blob: &[u8], layout: &MoveTypeLayout) -> Option<Value> {
        bcs::from_bytes_seed(SeedWrapper { layout }, blob).ok()
    }
    *)

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
    (* NOTE:
    The whole process should be:
    - resolver gets a `Constant` and we get its type of SignatureToken
    - preprocess the type from SignatureToken into a almost identical "layout" and return None if the type is wrong 
    - Now that we're provided the raw data of [u8] in constant and the processed layout type, we use the deserializer
      to eventually get a `Result` of `Value`
    
    Since eventually we involves external libray, here we just axiomatize the serialize/deserialize function
    *)
    Definition deserialize_constant (constant : Constant.t) : option Value.t. Admitted.

  End Impl_Value.
End Value.

(* pub struct Locals(Rc<RefCell<Vec<ValueImpl>>>); *)
Module Locals.
  Definition t := list ValueImpl.t.

  Module Lens.
  End Lens.

  Module Impl_Locals.
    Definition Self := move_sui.simulations.move_vm_types.values.values_impl.Locals.t.

    Definition default_valueimpl := ValueImpl.Invalid.

    (* 
    pub fn copy_loc(&self, idx: usize) -> PartialVMResult<Value> {
        let v = self.0.borrow();
        match v.get(idx) {
            Some(ValueImpl::Invalid) => Err(PartialVMError::new(
                StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR,
            )
            .with_message(format!("cannot copy invalid value at index {}", idx))),
            Some(v) => Ok(Value(v.copy_value()?)),
            None => Err(
                PartialVMError::new(StatusCode::VERIFIER_INVARIANT_VIOLATION).with_message(
                    format!("local index out of bounds: got {}, len: {}", idx, v.len()),
                ),
            ),
        }
    }
    *)
    Definition copy_loc (self : Self) (idx : Z) : PartialVMResult.t Value.t :=
      (* idx is out of range, which is the 3rd case for the match clause *)
      if Z.of_nat $ List.length self <=? idx
      then Result.Err $ PartialVMError.Impl_PartialVMError.new
        StatusCode.VERIFIER_INVARIANT_VIOLATION
      else
      (* Now we deal with the former 2 cases *)
        let v := List.nth (Z.to_nat idx) self default_valueimpl in
        match v with
        | ValueImpl.Invalid => Result.Err $ PartialVMError.Impl_PartialVMError.new
          StatusCode.UNKNOWN_INVARIANT_VIOLATION_ERROR
        | _ => Result.Ok $ v
        end.

    (* 
    fn swap_loc(&mut self, idx: usize, x: Value, violation_check: bool) -> PartialVMResult<Value> {
        let mut v = self.0.borrow_mut();
        match v.get_mut(idx) {
            Some(v) => {
                if violation_check {
                    if let ValueImpl::Container(c) = v {
                        if c.rc_count() > 1 {
                            return Err(PartialVMError::new(
                                StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR,
                            )
                            .with_message(
                                "moving container with dangling references".to_string(),
                            ));
                        }
                    }
                }
                Ok(Value(std::mem::replace(v, x.0)))
            }
            None => Err(
                PartialVMError::new(StatusCode::VERIFIER_INVARIANT_VIOLATION).with_message(
                    format!("local index out of bounds: got {}, len: {}", idx, v.len()),
                ),
            ),
        }
    }
    *)
    (* Helper function for `swap_loc`. Assumptions has been made that the idx never out ranges *)
    Fixpoint swap_list_nth {A : Set} (l : list A) (a : A) (idx : nat) : list A :=
      match idx with
      | O => a :: List.tl l
      | S idx => match List.head l with
        | Some h => h :: swap_list_nth (List.tl l) a idx
        | None => []
        end
      end.

    Definition swap_loc (idx : Z) (violation_check : bool) 
      : MS? (Self * Value.t) string (PartialVMResult.t Value.t) :=
      letS? '(v, x) := readS? in
      if Z.of_nat $ List.length v <=? idx
      then returnS? $ Result.Err $ 
        PartialVMError.Impl_PartialVMError.new StatusCode.VERIFIER_INVARIANT_VIOLATION
      else
        let v_nth := List.nth (Z.to_nat idx) v default_valueimpl in
        if violation_check
        then
        (* NOTE: we ignore the case where rc_counter is greater than 1. Might find a way to deal with it in the future *)
        let v_new := swap_list_nth v x (Z.to_nat idx) in
        letS? _ := writeS? (v_new, v_nth) in
          returnS? $ Result.Ok $ v_nth
        else
          returnS? $ Result.Err $ PartialVMError.Impl_PartialVMError.new StatusCode.VERIFIER_INVARIANT_VIOLATION.

    (*
    pub fn move_loc(&mut self, idx: usize, violation_check: bool) -> PartialVMResult<Value> {
        match self.swap_loc(idx, Value(ValueImpl::Invalid), violation_check)? {
            Value(ValueImpl::Invalid) => Err(PartialVMError::new(
                StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR,
            )
            .with_message(format!("cannot move invalid value at index {}", idx))),
            v => Ok(v),
        }
    }
    *)
    (* TODO: Define lens of Self to Self * Value *)
    Definition move_loc (idx : Z) (violation_check : bool) 
      : MS? Self string (PartialVMResult.t Value.t). Admitted.
        

    (* 
    pub fn store_loc(
        &mut self,
        idx: usize,
        x: Value,
        violation_check: bool,
    ) -> PartialVMResult<()> {
        self.swap_loc(idx, x, violation_check)?;
        Ok(())
    }
    *)
    Definition store_loc : Set. Admitted.

    (* 
      pub fn borrow_loc(&self, idx: usize) -> PartialVMResult<Value> {
        // TODO: this is very similar to SharedContainer::borrow_elem. Find a way to
        // reuse that code?

        let v = self.0.borrow();
        if idx >= v.len() {
            return Err(
                PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR).with_message(
                    format!(
                        "index out of bounds when borrowing local: got: {}, len: {}",
                        idx,
                        v.len()
                    ),
                ),
            );
        }

        match &v[idx] {
            ValueImpl::Container(c) => Ok(Value(ValueImpl::ContainerRef(ContainerRef::Local(
                c.copy_by_ref(),
            )))),

            ValueImpl::U8(_)
            | ValueImpl::U16(_)
            | ValueImpl::U32(_)
            | ValueImpl::U64(_)
            | ValueImpl::U128(_)
            | ValueImpl::U256(_)
            | ValueImpl::Bool(_)
            | ValueImpl::Address(_) => Ok(Value(ValueImpl::IndexedRef(IndexedRef {
                container_ref: ContainerRef::Local(Container::Locals(Rc::clone(&self.0))),
                idx,
            }))),

            ValueImpl::ContainerRef(_) | ValueImpl::Invalid | ValueImpl::IndexedRef(_) => Err(
                PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
                    .with_message(format!("cannot borrow local {:?}", &v[idx])),
            ),
        }
    }
    *)
    Definition borrow_loc : Set. Admitted.
  End Impl_Locals.
End Locals.
