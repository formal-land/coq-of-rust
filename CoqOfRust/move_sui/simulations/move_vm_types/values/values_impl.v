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
  - Implement `Reference`:
    - borrow_field
    - value_view
    - write_ref
    - read_ref
*)

(* NOTE(STUB): Only implement if necessary *)
Module Constant.
  Parameter t : Set.
End Constant.

Module AccountAddress.
  Parameter t : Set.
End AccountAddress.

Module GlobalDataStatus.
  Parameter t : Set.
End GlobalDataStatus.

(* **************** *)

(* 
/// A container is a collection of values. It is used to represent data structures like a
/// Move vector or struct.
///
/// There is one general container that can be used to store an array of any values, same
/// type or not, and a few specialized flavors to offer compact memory layout for small
/// primitive types.
///
/// Except when not owned by the VM stack, a container always lives inside an Rc<RefCell<>>,
/// making it possible to be shared by references.
#[derive(Debug, Clone)]
enum Container {
    Locals(Rc<RefCell<Vec<ValueImpl>>>),
    Vec(Rc<RefCell<Vec<ValueImpl>>>),
    Struct(Rc<RefCell<Vec<ValueImpl>>>),
    VecU8(Rc<RefCell<Vec<u8>>>),
    VecU64(Rc<RefCell<Vec<u64>>>),
    VecU128(Rc<RefCell<Vec<u128>>>),
    VecBool(Rc<RefCell<Vec<bool>>>),
    VecAddress(Rc<RefCell<Vec<AccountAddress>>>),
    VecU16(Rc<RefCell<Vec<u16>>>),
    VecU32(Rc<RefCell<Vec<u32>>>),
    VecU256(Rc<RefCell<Vec<u256::U256>>>),
}
*)
Module Container.

  Module ValueImpl.
    Parameter t : Set.
  End ValueImpl.

  Inductive t : Set :=
  (* TODO: Resolve mutual dependency issue below *)
  | Locals : list ValueImpl.t -> t
  | Vec : list ValueImpl.t -> t
  | Struct : list ValueImpl.t -> t
  | VecU8 : list Z -> t
  | VecU64 : list Z -> t
  | VecU128 : list Z -> t
  | VecBool : list bool -> t
  | VecAddress : list AccountAddress.t -> t
  | VecU16 : list Z -> t
  | VecU32 : list Z -> t
  | VecU256 : list Z -> t
  .
End Container.

(* 
/// A ContainerRef is a direct reference to a container, which could live either in the frame
/// or in global storage. In the latter case, it also keeps a status flag indicating whether
/// the container has been possibly modified.
#[derive(Debug)]
enum ContainerRef {
    Local(Container),
    Global {
        status: Rc<RefCell<GlobalDataStatus>>,
        container: Container,
    },
}
*)
Module ContainerRef.
  Record __Global : Set := {
    status : GlobalDataStatus.t;
    container: Container.t;
  }.

  Inductive t : Set :=
  | Local : Container.t -> t
  | _Global : __Global -> t
  .

  (* NOTE: This function is ignored
  fn copy_by_ref(&self) -> Self {
      match self {
          Self::Vec(r) => Self::Vec(Rc::clone(r)),
          Self::Struct(r) => Self::Struct(Rc::clone(r)),
          Self::VecU8(r) => Self::VecU8(Rc::clone(r)),
          Self::VecU16(r) => Self::VecU16(Rc::clone(r)),
          Self::VecU32(r) => Self::VecU32(Rc::clone(r)),
          Self::VecU64(r) => Self::VecU64(Rc::clone(r)),
          Self::VecU128(r) => Self::VecU128(Rc::clone(r)),
          Self::VecU256(r) => Self::VecU256(Rc::clone(r)),
          Self::VecBool(r) => Self::VecBool(Rc::clone(r)),
          Self::VecAddress(r) => Self::VecAddress(Rc::clone(r)),
          Self::Locals(r) => Self::Locals(Rc::clone(r)),
      }
  }
  *)
End ContainerRef.

(* 
/// A Move reference pointing to an element in a container.
#[derive(Debug)]
struct IndexedRef {
    idx: usize,
    container_ref: ContainerRef,
}
*)
Module IndexedRef.
  Record t : Set := {
    idx : Z;
    container_ref : ContainerRef.t;
  }.
End IndexedRef.

(* 
/// An umbrella enum for references. It is used to hide the internals of the public type
/// Reference.
#[derive(Debug)]
enum ReferenceImpl {
    IndexedRef(IndexedRef),
    ContainerRef(ContainerRef),
}
*)
Module ReferenceImpl.
  Inductive t : Set :=
  | IndexedRef : IndexedRef.t -> t
  | ContainerRef : ContainerRef.t -> t
  .
End ReferenceImpl.

(* 
/// A generic Move reference that offers two functionalities: read_ref & write_ref.
#[derive(Debug)]
pub struct Reference(ReferenceImpl);
*)
Module Reference.
  Definition t := ReferenceImpl.t.
End Reference.

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

(* 
pub trait VMValueCast<T> {
  fn cast(self) -> PartialVMResult<T>;
}
*)
Module VMValueCast.
  (* We can ignore `Self`, but for ordering issue a `Value.t` type should be provided *)
  Class Trait (Self result_type : Set) : Set := { 
    cast : Self -> PartialVMResult.t result_type;
  }.
End VMValueCast.

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
  Module Impl_Value.
    Definition Self := move_sui.simulations.move_vm_types.values.values_impl.Value.t.
    Module cast.
      Global Instance cast_u8 : VMValueCast.Trait Self Z : Set := {
        cast (self : Self) := match self with
          | ValueImpl.U8 x => Result.Ok x
          | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
          end;
      }.

      Global Instance cast_u16 : VMValueCast.Trait Self Z : Set := {
        cast (self : Self) := match self with
          | ValueImpl.U16 x => Result.Ok x
          | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
          end;
      }.

      Global Instance cast_u32 : VMValueCast.Trait Self Z : Set := {
        cast (self : Self) := match self with
          | ValueImpl.U32 x => Result.Ok x
          | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
          end;
      }.

      Global Instance cast_u64 : VMValueCast.Trait Self Z : Set := {
        cast (self : Self) := match self with
          | ValueImpl.U64 x => Result.Ok x
          | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
          end;
      }.

      Global Instance cast_u128 : VMValueCast.Trait Self Z : Set := {
        cast (self : Self) := match self with
          | ValueImpl.U128 x => Result.Ok x
          | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
          end;
      }.

      Global Instance cast_u256 : VMValueCast.Trait Self Z : Set := {
        cast (self : Self) := match self with
          | ValueImpl.U256 x => Result.Ok x
          | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
          end;
      }.

      Global Instance cast_bool : VMValueCast.Trait Self bool : Set := {
        cast (self : Self) := match self with
          | ValueImpl.Bool x => Result.Ok x
          | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
          end;
      }.

      Global Instance cast_AccountAddress : VMValueCast.Trait Self AccountAddress.t : Set := {
        cast (self : Self) := match self with
          | ValueImpl.Address x => Result.Ok x
          | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
          end;
      }.

      Global Instance cast_ContainerRef : VMValueCast.Trait Self ContainerRef.t : Set := {
        cast (self : Self) := match self with
          | ValueImpl.ContainerRef x => Result.Ok x
          | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
          end;
      }.

      Global Instance cast_IndexedRef : VMValueCast.Trait Self IndexedRef.t : Set := {
        cast (self : Self) := match self with
          | ValueImpl.IndexedRef x => Result.Ok x
          | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
          end;
      }.
    End cast.

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

  Definition coerce_Container_Locals (c : Container.ValueImpl.t) : t. Admitted.
  Definition coerce_Locals_Container (self : t) : Container.ValueImpl.t. Admitted.
End Value.

(* pub struct StructRef(ContainerRef); *)
Module StructRef.
  Definition t := ContainerRef.t.

  Module Impl_StructRef.
    Definition Self := move_sui.simulations.move_vm_types.values.values_impl.StructRef.t.
    (* 
    impl StructRef {
        pub fn borrow_field(&self, idx: usize) -> PartialVMResult<Value> {
            Ok(Value(self.0.borrow_elem(idx)?))
        }
    }
    *)
    Definition borrow_field : Set. Admitted.

    (* 
    impl VMValueCast<StructRef> for Value {
        fn cast(self) -> PartialVMResult<StructRef> {
            Ok(StructRef(VMValueCast::cast(self)?))
        }
    }
    *)
    Global Instance cast_StructRef : VMValueCast.Trait Value.t StructRef.t : Set := {
      cast self := VMValueCast.cast self;
    }.
  End Impl_StructRef.
End StructRef.

(* pub struct Locals(Rc<RefCell<Vec<ValueImpl>>>); *)
Module Locals.
  Definition t := list ValueImpl.t.

  Module Lens.
    Definition lens_self_self_value (v : Value.t) : Lens.t t (t * Value.t) := {|
      Lens.read self := (self, v);
      Lens.write self state := fst state;
    |}.
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
      then Result.Err $ PartialVMError.new
        StatusCode.VERIFIER_INVARIANT_VIOLATION
      else
      (* Now we deal with the former 2 cases *)
        let v := List.nth (Z.to_nat idx) self default_valueimpl in
        match v with
        | ValueImpl.Invalid => Result.Err $ PartialVMError.new
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
      : MS! (Self * Value.t) (PartialVMResult.t Value.t) :=
      letS! (v, x) := readS! in
      if Z.of_nat $ List.length v <=? idx
      then returnS! $ Result.Err $ 
        PartialVMError.new StatusCode.VERIFIER_INVARIANT_VIOLATION
      else
        let v_nth := List.nth (Z.to_nat idx) v default_valueimpl in
        if violation_check
        then
        (* NOTE: we ignore the case where rc_counter is greater than 1. Might find a way to deal with it in the future *)
        let v_new := swap_list_nth v x (Z.to_nat idx) in
        letS! _ := writeS! (v_new, v_nth) in
          returnS! $ Result.Ok $ v_nth
        else
          returnS! $ Result.Err $ PartialVMError.new StatusCode.VERIFIER_INVARIANT_VIOLATION.

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
    Definition move_loc (idx : Z) (violation_check : bool) 
      : MS! Self (PartialVMResult.t Value.t) :=
      letS!? result := liftS! (Lens.lens_self_self_value ValueImpl.Invalid) 
        $ swap_loc idx violation_check in
      match result with
      | ValueImpl.Invalid => returnS! $ Result.Err $ 
        PartialVMError.new StatusCode.VERIFIER_INVARIANT_VIOLATION
      | v => returnS! $ Result.Ok v
      end.

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
    Definition store_loc (idx : Z) (violation_check : bool) 
      : MS! (Self * Value.t) (PartialVMResult.t unit) :=
      letS!? result := swap_loc idx violation_check in
        returnS! $ Result.Ok tt.

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
    Definition borrow_loc (self : Self) (idx : Z) : PartialVMResult.t Value.t. Admitted.
    (* Definition borrow_loc (self : Self) (idx : Z) : PartialVMResult.t Value.t :=
      let v := self in
      if Z.of_nat $ List.length self >=? idx
      then Result.Err $ PartialVMError.new 
        StatusCode.UNKNOWN_INVARIANT_VIOLATION_ERROR
      else
        let v_nth := List.nth (Z.to_nat idx) self default_valueimpl in
        let result_1 := Result.Ok $ ValueImpl.IndexedRef $ 
          IndexedRef.Build_t 
            (* TODO: resolve here the mutual dependency issue *)
            (* NOTE: How should we directly construct a mutual dependent item? *)
            (ContainerRef.Local $ Container.Locals (Value.coerce_Container_Locals self))
            idx in
        let result_2 := Result.Err $ PartialVMError.new 
          StatusCode.UNKNOWN_INVARIANT_VIOLATION_ERROR in
        match v_nth with
        | ValueImpl.Container c =>
          returnS! $ Result.Ok $ ValueImpl.ContainerRef $ ContainerRef.Local c
        | ValueImpl.U8 _ => returnS! result_1
        | ValueImpl.U16 _ => returnS! result_1
        | ValueImpl.U32 _ => returnS! result_1
        | ValueImpl.U64 _ => returnS! result_1
        | ValueImpl.U128 _ => returnS! result_1
        | ValueImpl.U256 _ => returnS! result_1
        | ValueImpl.Bool _ => returnS! result_1
        | ValueImpl.Address _ => returnS! result_1
        | ValueImpl.ContainerRef _ => result_2
        | ValueImpl.Invalid => result_2
        | ValueImpl.IndexedRef _ => result_2
        end
        . *)
  End Impl_Locals.
End Locals.

(*
impl IntegerValue {
    pub fn add_checked(self, other: Self) -> PartialVMResult<Self> {
        use IntegerValue::*;
        let res = match (self, other) {
            (U8(l), U8(r)) => u8::checked_add(l, r).map(IntegerValue::U8),
            (U16(l), U16(r)) => u16::checked_add(l, r).map(IntegerValue::U16),
            (U32(l), U32(r)) => u32::checked_add(l, r).map(IntegerValue::U32),
            (U64(l), U64(r)) => u64::checked_add(l, r).map(IntegerValue::U64),
            (U128(l), U128(r)) => u128::checked_add(l, r).map(IntegerValue::U128),
            (U256(l), U256(r)) => u256::U256::checked_add(l, r).map(IntegerValue::U256),
            (l, r) => {
                let msg = format!("Cannot add {:?} and {:?}", l, r);
                return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
            }
        };
        res.ok_or_else(|| PartialVMError::new(StatusCode::ARITHMETIC_ERROR))
    }

    pub fn sub_checked(self, other: Self) -> PartialVMResult<Self> {
        use IntegerValue::*;
        let res = match (self, other) {
            (U8(l), U8(r)) => u8::checked_sub(l, r).map(IntegerValue::U8),
            (U16(l), U16(r)) => u16::checked_sub(l, r).map(IntegerValue::U16),
            (U32(l), U32(r)) => u32::checked_sub(l, r).map(IntegerValue::U32),
            (U64(l), U64(r)) => u64::checked_sub(l, r).map(IntegerValue::U64),
            (U128(l), U128(r)) => u128::checked_sub(l, r).map(IntegerValue::U128),
            (U256(l), U256(r)) => u256::U256::checked_sub(l, r).map(IntegerValue::U256),
            (l, r) => {
                let msg = format!("Cannot sub {:?} from {:?}", r, l);
                return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
            }
        };
        res.ok_or_else(|| PartialVMError::new(StatusCode::ARITHMETIC_ERROR))
    }

    pub fn mul_checked(self, other: Self) -> PartialVMResult<Self> {
        use IntegerValue::*;
        let res = match (self, other) {
            (U8(l), U8(r)) => u8::checked_mul(l, r).map(IntegerValue::U8),
            (U16(l), U16(r)) => u16::checked_mul(l, r).map(IntegerValue::U16),
            (U32(l), U32(r)) => u32::checked_mul(l, r).map(IntegerValue::U32),
            (U64(l), U64(r)) => u64::checked_mul(l, r).map(IntegerValue::U64),
            (U128(l), U128(r)) => u128::checked_mul(l, r).map(IntegerValue::U128),
            (U256(l), U256(r)) => u256::U256::checked_mul(l, r).map(IntegerValue::U256),
            (l, r) => {
                let msg = format!("Cannot mul {:?} and {:?}", l, r);
                return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
            }
        };
        res.ok_or_else(|| PartialVMError::new(StatusCode::ARITHMETIC_ERROR))
    }

    pub fn div_checked(self, other: Self) -> PartialVMResult<Self> {
        use IntegerValue::*;
        let res = match (self, other) {
            (U8(l), U8(r)) => u8::checked_div(l, r).map(IntegerValue::U8),
            (U16(l), U16(r)) => u16::checked_div(l, r).map(IntegerValue::U16),
            (U32(l), U32(r)) => u32::checked_div(l, r).map(IntegerValue::U32),
            (U64(l), U64(r)) => u64::checked_div(l, r).map(IntegerValue::U64),
            (U128(l), U128(r)) => u128::checked_div(l, r).map(IntegerValue::U128),
            (U256(l), U256(r)) => u256::U256::checked_div(l, r).map(IntegerValue::U256),
            (l, r) => {
                let msg = format!("Cannot div {:?} by {:?}", l, r);
                return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
            }
        };
        res.ok_or_else(|| PartialVMError::new(StatusCode::ARITHMETIC_ERROR))
    }

    pub fn rem_checked(self, other: Self) -> PartialVMResult<Self> {
        use IntegerValue::*;
        let res = match (self, other) {
            (U8(l), U8(r)) => u8::checked_rem(l, r).map(IntegerValue::U8),
            (U16(l), U16(r)) => u16::checked_rem(l, r).map(IntegerValue::U16),
            (U32(l), U32(r)) => u32::checked_rem(l, r).map(IntegerValue::U32),
            (U64(l), U64(r)) => u64::checked_rem(l, r).map(IntegerValue::U64),
            (U128(l), U128(r)) => u128::checked_rem(l, r).map(IntegerValue::U128),
            (U256(l), U256(r)) => u256::U256::checked_rem(l, r).map(IntegerValue::U256),
            (l, r) => {
                let msg = format!("Cannot rem {:?} by {:?}", l, r);
                return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
            }
        };
        res.ok_or_else(|| PartialVMError::new(StatusCode::ARITHMETIC_ERROR))
    }

    pub fn bit_or(self, other: Self) -> PartialVMResult<Self> {
        use IntegerValue::*;
        Ok(match (self, other) {
            (U8(l), U8(r)) => IntegerValue::U8(l | r),
            (U16(l), U16(r)) => IntegerValue::U16(l | r),
            (U32(l), U32(r)) => IntegerValue::U32(l | r),
            (U64(l), U64(r)) => IntegerValue::U64(l | r),
            (U128(l), U128(r)) => IntegerValue::U128(l | r),
            (U256(l), U256(r)) => IntegerValue::U256(l | r),
            (l, r) => {
                let msg = format!("Cannot bit_or {:?} and {:?}", l, r);
                return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
            }
        })
    }

    pub fn bit_and(self, other: Self) -> PartialVMResult<Self> {
        use IntegerValue::*;
        Ok(match (self, other) {
            (U8(l), U8(r)) => IntegerValue::U8(l & r),
            (U16(l), U16(r)) => IntegerValue::U16(l & r),
            (U32(l), U32(r)) => IntegerValue::U32(l & r),
            (U64(l), U64(r)) => IntegerValue::U64(l & r),
            (U128(l), U128(r)) => IntegerValue::U128(l & r),
            (U256(l), U256(r)) => IntegerValue::U256(l & r),
            (l, r) => {
                let msg = format!("Cannot bit_and {:?} and {:?}", l, r);
                return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
            }
        })
    }

    pub fn bit_xor(self, other: Self) -> PartialVMResult<Self> {
        use IntegerValue::*;
        Ok(match (self, other) {
            (U8(l), U8(r)) => IntegerValue::U8(l ^ r),
            (U16(l), U16(r)) => IntegerValue::U16(l ^ r),
            (U32(l), U32(r)) => IntegerValue::U32(l ^ r),
            (U64(l), U64(r)) => IntegerValue::U64(l ^ r),
            (U128(l), U128(r)) => IntegerValue::U128(l ^ r),
            (U256(l), U256(r)) => IntegerValue::U256(l ^ r),
            (l, r) => {
                let msg = format!("Cannot bit_xor {:?} and {:?}", l, r);
                return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
            }
        })
    }

    pub fn shl_checked(self, n_bits: u8) -> PartialVMResult<Self> {
        use IntegerValue::*;

        Ok(match self {
            U8(x) => {
                if n_bits >= 8 {
                    return Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR));
                }
                IntegerValue::U8(x << n_bits)
            }
            U16(x) => {
                if n_bits >= 16 {
                    return Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR));
                }
                IntegerValue::U16(x << n_bits)
            }
            U32(x) => {
                if n_bits >= 32 {
                    return Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR));
                }
                IntegerValue::U32(x << n_bits)
            }
            U64(x) => {
                if n_bits >= 64 {
                    return Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR));
                }
                IntegerValue::U64(x << n_bits)
            }
            U128(x) => {
                if n_bits >= 128 {
                    return Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR));
                }
                IntegerValue::U128(x << n_bits)
            }
            U256(x) => IntegerValue::U256(x << n_bits),
        })
    }

    pub fn shr_checked(self, n_bits: u8) -> PartialVMResult<Self> {
        use IntegerValue::*;

        Ok(match self {
            U8(x) => {
                if n_bits >= 8 {
                    return Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR));
                }
                IntegerValue::U8(x >> n_bits)
            }
            U16(x) => {
                if n_bits >= 16 {
                    return Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR));
                }
                IntegerValue::U16(x >> n_bits)
            }
            U32(x) => {
                if n_bits >= 32 {
                    return Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR));
                }
                IntegerValue::U32(x >> n_bits)
            }
            U64(x) => {
                if n_bits >= 64 {
                    return Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR));
                }
                IntegerValue::U64(x >> n_bits)
            }
            U128(x) => {
                if n_bits >= 128 {
                    return Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR));
                }
                IntegerValue::U128(x >> n_bits)
            }
            U256(x) => IntegerValue::U256(x >> n_bits),
        })
    }

    pub fn lt(self, other: Self) -> PartialVMResult<bool> {
        use IntegerValue::*;

        Ok(match (self, other) {
            (U8(l), U8(r)) => l < r,
            (U16(l), U16(r)) => l < r,
            (U32(l), U32(r)) => l < r,
            (U64(l), U64(r)) => l < r,
            (U128(l), U128(r)) => l < r,
            (U256(l), U256(r)) => l < r,
            (l, r) => {
                let msg = format!(
                    "Cannot compare {:?} and {:?}: incompatible integer types",
                    l, r
                );
                return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
            }
        })
    }

    pub fn le(self, other: Self) -> PartialVMResult<bool> {
        use IntegerValue::*;

        Ok(match (self, other) {
            (U8(l), U8(r)) => l <= r,
            (U16(l), U16(r)) => l <= r,
            (U32(l), U32(r)) => l <= r,
            (U64(l), U64(r)) => l <= r,
            (U128(l), U128(r)) => l <= r,
            (U256(l), U256(r)) => l <= r,
            (l, r) => {
                let msg = format!(
                    "Cannot compare {:?} and {:?}: incompatible integer types",
                    l, r
                );
                return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
            }
        })
    }

    pub fn gt(self, other: Self) -> PartialVMResult<bool> {
        use IntegerValue::*;

        Ok(match (self, other) {
            (U8(l), U8(r)) => l > r,
            (U16(l), U16(r)) => l > r,
            (U32(l), U32(r)) => l > r,
            (U64(l), U64(r)) => l > r,
            (U128(l), U128(r)) => l > r,
            (U256(l), U256(r)) => l > r,
            (l, r) => {
                let msg = format!(
                    "Cannot compare {:?} and {:?}: incompatible integer types",
                    l, r
                );
                return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
            }
        })
    }

    pub fn ge(self, other: Self) -> PartialVMResult<bool> {
        use IntegerValue::*;

        Ok(match (self, other) {
            (U8(l), U8(r)) => l >= r,
            (U16(l), U16(r)) => l >= r,
            (U32(l), U32(r)) => l >= r,
            (U64(l), U64(r)) => l >= r,
            (U128(l), U128(r)) => l >= r,
            (U256(l), U256(r)) => l >= r,
            (l, r) => {
                let msg = format!(
                    "Cannot compare {:?} and {:?}: incompatible integer types",
                    l, r
                );
                return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
            }
        })
    }

    pub fn into_value(self) -> Value {
        use IntegerValue::*;

        match self {
            U8(x) => Value::u8(x),
            U16(x) => Value::u16(x),
            U32(x) => Value::u32(x),
            U64(x) => Value::u64(x),
            U128(x) => Value::u128(x),
            U256(x) => Value::u256(x),
        }
    }
}

impl IntegerValue {
    pub fn cast_u8(self) -> PartialVMResult<u8> {
        use IntegerValue::*;

        match self {
            U8(x) => Ok(x),
            U16(x) => {
                if x > (std::u8::MAX as u16) {
                    Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR)
                        .with_message(format!("Cannot cast u16({}) to u8", x)))
                } else {
                    Ok(x as u8)
                }
            }
            U32(x) => {
                if x > (std::u8::MAX as u32) {
                    Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR)
                        .with_message(format!("Cannot cast u32({}) to u8", x)))
                } else {
                    Ok(x as u8)
                }
            }
            U64(x) => {
                if x > (std::u8::MAX as u64) {
                    Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR)
                        .with_message(format!("Cannot cast u64({}) to u8", x)))
                } else {
                    Ok(x as u8)
                }
            }
            U128(x) => {
                if x > (std::u8::MAX as u128) {
                    Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR)
                        .with_message(format!("Cannot cast u128({}) to u8", x)))
                } else {
                    Ok(x as u8)
                }
            }
            U256(x) => {
                if x > (u256::U256::from(std::u8::MAX)) {
                    Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR)
                        .with_message(format!("Cannot cast u256({}) to u8", x)))
                } else {
                    Ok(x.unchecked_as_u8())
                }
            }
        }
    }

    pub fn cast_u16(self) -> PartialVMResult<u16> {
        use IntegerValue::*;

        match self {
            U8(x) => Ok(x as u16),
            U16(x) => Ok(x),
            U32(x) => {
                if x > (std::u16::MAX as u32) {
                    Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR)
                        .with_message(format!("Cannot cast u32({}) to u16", x)))
                } else {
                    Ok(x as u16)
                }
            }
            U64(x) => {
                if x > (std::u16::MAX as u64) {
                    Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR)
                        .with_message(format!("Cannot cast u64({}) to u16", x)))
                } else {
                    Ok(x as u16)
                }
            }
            U128(x) => {
                if x > (std::u16::MAX as u128) {
                    Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR)
                        .with_message(format!("Cannot cast u128({}) to u16", x)))
                } else {
                    Ok(x as u16)
                }
            }
            U256(x) => {
                if x > (u256::U256::from(std::u16::MAX)) {
                    Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR)
                        .with_message(format!("Cannot cast u256({}) to u16", x)))
                } else {
                    Ok(x.unchecked_as_u16())
                }
            }
        }
    }

    pub fn cast_u32(self) -> PartialVMResult<u32> {
        use IntegerValue::*;

        match self {
            U8(x) => Ok(x as u32),
            U16(x) => Ok(x as u32),
            U32(x) => Ok(x),
            U64(x) => {
                if x > (std::u32::MAX as u64) {
                    Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR)
                        .with_message(format!("Cannot cast u64({}) to u32", x)))
                } else {
                    Ok(x as u32)
                }
            }
            U128(x) => {
                if x > (std::u32::MAX as u128) {
                    Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR)
                        .with_message(format!("Cannot cast u128({}) to u32", x)))
                } else {
                    Ok(x as u32)
                }
            }
            U256(x) => {
                if x > (u256::U256::from(std::u32::MAX)) {
                    Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR)
                        .with_message(format!("Cannot cast u128({}) to u32", x)))
                } else {
                    Ok(x.unchecked_as_u32())
                }
            }
        }
    }

    pub fn cast_u64(self) -> PartialVMResult<u64> {
        use IntegerValue::*;

        match self {
            U8(x) => Ok(x as u64),
            U16(x) => Ok(x as u64),
            U32(x) => Ok(x as u64),
            U64(x) => Ok(x),
            U128(x) => {
                if x > (std::u64::MAX as u128) {
                    Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR)
                        .with_message(format!("Cannot cast u128({}) to u64", x)))
                } else {
                    Ok(x as u64)
                }
            }
            U256(x) => {
                if x > (u256::U256::from(std::u64::MAX)) {
                    Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR)
                        .with_message(format!("Cannot cast u256({}) to u64", x)))
                } else {
                    Ok(x.unchecked_as_u64())
                }
            }
        }
    }

    pub fn cast_u128(self) -> PartialVMResult<u128> {
        use IntegerValue::*;

        match self {
            U8(x) => Ok(x as u128),
            U16(x) => Ok(x as u128),
            U32(x) => Ok(x as u128),
            U64(x) => Ok(x as u128),
            U128(x) => Ok(x),
            U256(x) => {
                if x > (u256::U256::from(std::u128::MAX)) {
                    Err(PartialVMError::new(StatusCode::ARITHMETIC_ERROR)
                        .with_message(format!("Cannot cast u256({}) to u128", x)))
                } else {
                    Ok(x.unchecked_as_u128())
                }
            }
        }
    }

    pub fn cast_u256(self) -> PartialVMResult<u256::U256> {
        use IntegerValue::*;

        Ok(match self {
            U8(x) => u256::U256::from(x),
            U16(x) => u256::U256::from(x),
            U32(x) => u256::U256::from(x),
            U64(x) => u256::U256::from(x),
            U128(x) => u256::U256::from(x),
            U256(x) => x,
        })
    }
}
*)

