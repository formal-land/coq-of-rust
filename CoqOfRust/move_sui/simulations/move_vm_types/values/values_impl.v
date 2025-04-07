Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import simulations.M.
Require Import CoqOfRust.lib.lib.

Require CoqOfRust.move_sui.simulations.move_binary_format.errors.
Module PartialVMResult := errors.PartialVMResult.
Module PartialVMError := errors.PartialVMError.

Require CoqOfRust.move_sui.simulations.move_core_types.vm_status.
Module StatusCode := vm_status.StatusCode.

Require Import CoqOfRust.move_sui.simulations.move_binary_format.file_format.

(* TODO(progress): 
  - Implement `Reference`:
    - borrow_field
    - value_view
    - write_ref
    - read_ref
*)

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
Module ContainerSkeleton.
  Inductive t {ValueImpl : Set} : Set :=
  | Locals (locals : list ValueImpl)
  | Vec (vec : list ValueImpl)
  | Struct (fields : list ValueImpl)
  | VecU8 (vec : list Z)
  | VecU64 (vec : list Z)
  | VecU128 (vec : list Z)
  | VecBool (vec : list bool)
  | VecAddress (vec : list AccountAddress.t)
  | VecU16 (vec : list Z)
  | VecU32 (vec : list Z)
  | VecU256 (vec : list Z)
  .
  Arguments t : clear implicits.
End ContainerSkeleton.

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
Module ContainerRefSkeleton.
  Module Global_.
    Record t {ValueImpl : Set} : Set := {
      status : GlobalDataStatus.t;
      container: ContainerSkeleton.t ValueImpl;
    }.
    Arguments t : clear implicits.
  End Global_.

  Inductive t {ValueImpl : Set} : Set :=
  | Local : ContainerSkeleton.t ValueImpl -> t
  | Global_ : Global_.t ValueImpl -> t
  .
  Arguments t : clear implicits.
End ContainerRefSkeleton.

(* 
/// A Move reference pointing to an element in a container.
#[derive(Debug)]
struct IndexedRef {
    idx: usize,
    container_ref: ContainerRef,
}
*)
Module IndexedRefSkeleton.
  Record t {ValueImpl : Set} : Set := {
    idx : Z;
    container_ref : ContainerRefSkeleton.t ValueImpl;
  }.
  Arguments t : clear implicits.
End IndexedRefSkeleton.

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
  | Container : ContainerSkeleton.t t -> t
  | ContainerRef : ContainerRefSkeleton.t t -> t
  | IndexedRef : IndexedRefSkeleton.t t -> t
  .
End ValueImpl.

Module Container.
  Definition t : Set := ContainerSkeleton.t ValueImpl.t.
End Container.

Module ContainerRef.
  Definition t : Set := ContainerRefSkeleton.t ValueImpl.t.
End ContainerRef.

Module IndexedRef.
  Definition t : Set := IndexedRefSkeleton.t ValueImpl.t.
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

Module Impl_ContainerRef.
  Definition Self : Set := ContainerRef.t.

  (*
  fn copy_value(&self) -> Self {
        match self {
            Self::Local(container) => Self::Local(container.copy_by_ref()),
            Self::Global { status, container } => Self::Global {
                status: Rc::clone(status),
                container: container.copy_by_ref(),
            },
        }
    }
  *)
  (* If we unroll the definition this is the identity function (ignoring the pointers) *)
  Definition copy_value (self : Self) : Self :=
    self.

  (*
  fn container(&self) -> &Container {
      match self {
          Self::Local(container) | Self::Global { container, .. } => container,
      }
  }
  *)
  Definition container (self : Self) : Container.t :=
    match self with
    | ContainerRefSkeleton.Local container
    | ContainerRefSkeleton.Global_ {| ContainerRefSkeleton.Global_.container := container |} =>
      container
    end.
End Impl_ContainerRef.

Module Impl_IndexedRef.
  Definition Self : Set := IndexedRef.t.

  (*
  fn copy_value(&self) -> Self {
        Self {
            idx: self.idx,
            container_ref: self.container_ref.copy_value(),
        }
    }
  *)
  (* If we unroll the definition this is the identity function (ignoring the pointers) *)
  Definition copy_value (self : Self) : Self :=
    self.
End Impl_IndexedRef.

Module Impl_ValueImpl.
  Definition Self : Set := ValueImpl.t.

  (*
  fn copy_value(&self) -> PartialVMResult<Self> {
        use ValueImpl::*;

        Ok(match self {
            Invalid => Invalid,

            U8(x) => U8( *x),
            U16(x) => U16( *x),
            U32(x) => U32( *x),
            U64(x) => U64( *x),
            U128(x) => U128( *x),
            U256(x) => U256( *x),
            Bool(x) => Bool( *x),
            Address(x) => Address( *x),

            ContainerRef(r) => ContainerRef(r.copy_value()),
            IndexedRef(r) => IndexedRef(r.copy_value()),

            // When cloning a container, we need to make sure we make a deep
            // copy of the data instead of a shallow copy of the Rc.
            Container(c) => Container(c.copy_value()?),
        })
    }
  *)
  Reserved Notation "'Container_copy_value".

  Fixpoint copy_value (self : Self) : PartialVMResult.t Self :=
    (* impl Container { *)
    (*
    fn copy_value(&self) -> PartialVMResult<Self> {
        let copy_rc_ref_vec_val = |r: &Rc<RefCell<Vec<ValueImpl>>>| {
            Ok(Rc::new(RefCell::new(
                r.borrow()
                    .iter()
                    .map(|v| v.copy_value())
                    .collect::<PartialVMResult<_>>()?,
            )))
        };

        Ok(match self {
            Self::Vec(r) => Self::Vec(copy_rc_ref_vec_val(r)?),
            Self::Struct(r) => Self::Struct(copy_rc_ref_vec_val(r)?),

            Self::VecU8(r) => Self::VecU8(Rc::new(RefCell::new(r.borrow().clone()))),
            Self::VecU16(r) => Self::VecU16(Rc::new(RefCell::new(r.borrow().clone()))),
            Self::VecU32(r) => Self::VecU32(Rc::new(RefCell::new(r.borrow().clone()))),
            Self::VecU64(r) => Self::VecU64(Rc::new(RefCell::new(r.borrow().clone()))),
            Self::VecU128(r) => Self::VecU128(Rc::new(RefCell::new(r.borrow().clone()))),
            Self::VecU256(r) => Self::VecU256(Rc::new(RefCell::new(r.borrow().clone()))),
            Self::VecBool(r) => Self::VecBool(Rc::new(RefCell::new(r.borrow().clone()))),
            Self::VecAddress(r) => Self::VecAddress(Rc::new(RefCell::new(r.borrow().clone()))),

            Self::Locals(_) => {
                return Err(
                    PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
                        .with_message("cannot copy a Locals container".to_string()),
                )
            }
        })
    }
    *)
    match self with
    | ValueImpl.Invalid => Result.Ok ValueImpl.Invalid
    | ValueImpl.U8 x => Result.Ok $ ValueImpl.U8 x
    | ValueImpl.U16 x => Result.Ok $ ValueImpl.U16 x
    | ValueImpl.U32 x => Result.Ok $ ValueImpl.U32 x
    | ValueImpl.U64 x => Result.Ok $ ValueImpl.U64 x
    | ValueImpl.U128 x => Result.Ok $ ValueImpl.U128 x
    | ValueImpl.U256 x => Result.Ok $ ValueImpl.U256 x
    | ValueImpl.Bool x => Result.Ok $ ValueImpl.Bool x
    | ValueImpl.Address x => Result.Ok $ ValueImpl.Address x
    | ValueImpl.ContainerRef r =>
      Result.Ok $ ValueImpl.ContainerRef (Impl_ContainerRef.copy_value r)
    | ValueImpl.IndexedRef r =>
      Result.Ok $ ValueImpl.IndexedRef (Impl_IndexedRef.copy_value r)
    | ValueImpl.Container c =>
      let? copy_value := 'Container_copy_value c in
      Result.Ok $ ValueImpl.Container copy_value
    end

    where "'Container_copy_value" := (fun (self : Container.t) =>
      match self with
      | ContainerSkeleton.Vec vec =>
        let? vec := Result.List.map copy_value vec in
        Result.Ok $ ContainerSkeleton.Vec vec
      | ContainerSkeleton.Struct f =>
        let? f := Result.List.map copy_value f in
        Result.Ok $ ContainerSkeleton.Struct f
      | ContainerSkeleton.VecU8 v => Result.Ok $ ContainerSkeleton.VecU8 v
      | ContainerSkeleton.VecU64 v => Result.Ok $ ContainerSkeleton.VecU64 v
      | ContainerSkeleton.VecU128 v => Result.Ok $ ContainerSkeleton.VecU128 v
      | ContainerSkeleton.VecBool v => Result.Ok $ ContainerSkeleton.VecBool v
      | ContainerSkeleton.VecAddress v => Result.Ok $ ContainerSkeleton.VecAddress v
      | ContainerSkeleton.VecU16 v => Result.Ok $ ContainerSkeleton.VecU16 v
      | ContainerSkeleton.VecU32 v => Result.Ok $ ContainerSkeleton.VecU32 v
      | ContainerSkeleton.VecU256 v => Result.Ok $ ContainerSkeleton.VecU256 v
      | ContainerSkeleton.Locals _ =>
        Result.Err $ PartialVMError.new StatusCode.UNKNOWN_INVARIANT_VIOLATION_ERROR
      end
    ).

  Definition Container_copy_value := 'Container_copy_value.

  (*
  fn equals(&self, other: &Self) -> PartialVMResult<bool> {
      use ValueImpl::*;

      let res = match (self, other) {
          (U8(l), U8(r)) => l == r,
          (U16(l), U16(r)) => l == r,
          (U32(l), U32(r)) => l == r,
          (U64(l), U64(r)) => l == r,
          (U128(l), U128(r)) => l == r,
          (U256(l), U256(r)) => l == r,
          (Bool(l), Bool(r)) => l == r,
          (Address(l), Address(r)) => l == r,

          (Container(l), Container(r)) => l.equals(r)?,

          (ContainerRef(l), ContainerRef(r)) => l.equals(r)?,
          (IndexedRef(l), IndexedRef(r)) => l.equals(r)?,
          (Invalid, _)
          | (U8(_), _)
          | (U16(_), _)
          | (U32(_), _)
          | (U64(_), _)
          | (U128(_), _)
          | (U256(_), _)
          | (Bool(_), _)
          | (Address(_), _)
          | (Container(_), _)
          | (ContainerRef(_), _)
          | (IndexedRef(_), _) => {
              return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
                  .with_message(format!("cannot compare values: {:?}, {:?}", self, other)))
          }
      };

      Ok(res)
  }
  *)
  Parameter equals : Self -> Self -> PartialVMResult.t bool.
End Impl_ValueImpl.

Module Impl_Container.
  Definition Self : Set := Container.t.

  Definition copy_value : Self -> PartialVMResult.t Self := Impl_ValueImpl.Container_copy_value.
End Impl_Container.

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
  Arguments t /.

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
    Definition Self := Value.t.
    Module cast.
      Global Instance cast_u8 : VMValueCast.Trait Self U8.t : Set := {
        cast (self : Self) := match self with
          | ValueImpl.U8 x => Result.Ok {| Integer.value := x |}
          | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
          end;
      }.

      Global Instance cast_u16 : VMValueCast.Trait Self U16.t : Set := {
        cast (self : Self) := match self with
          | ValueImpl.U16 x => Result.Ok {| Integer.value := x |}
          | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
          end;
      }.

      Global Instance cast_u32 : VMValueCast.Trait Self U32.t : Set := {
        cast (self : Self) := match self with
          | ValueImpl.U32 x => Result.Ok {| Integer.value := x |}
          | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
          end;
      }.

      Global Instance cast_u64 : VMValueCast.Trait Self U64.t : Set := {
        cast (self : Self) := match self with
          | ValueImpl.U64 x => Result.Ok {| Integer.value := x |}
          | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
          end;
      }.

      Global Instance cast_u128 : VMValueCast.Trait Self U128.t : Set := {
        cast (self : Self) := match self with
          | ValueImpl.U128 x => Result.Ok {| Integer.value := x |}
          | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
          end;
      }.

      (* Global Instance cast_u256 : VMValueCast.Trait Self Z : Set := {
        cast (self : Self) := match self with
          | ValueImpl.U256 x => Result.Ok x
          | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
          end;
      }. *)

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

  Definition coerce_Container_Locals (c : Value.t) : t. Admitted.
  Definition coerce_Locals_Container (self : t) : Value.t. Admitted.
End Value.

Module Impl_Value.
  (*
  pub fn deserialize_constant(constant: &Constant) -> Option<Value> {
      let layout = Self::constant_sig_token_to_layout(&constant.type_)?;
      Value::simple_deserialize(&constant.data, &layout)
  }
  *)
  (** We keep this function as axiom for now, as its definition would be quite complex and the
      details are not required for the verification of the type-checker. *)
  Parameter deserialize_constant : Constant.t -> option Value.t.
End Impl_Value.

Module Impl_ContainerRef'.
  Definition Self := ContainerRef.t.

  (*
  fn read_ref(self) -> PartialVMResult<Value> {
      Ok(Value(ValueImpl::Container(self.container().copy_value()?)))
  }
  *)
  Definition read_ref (self : Self) : PartialVMResult.t Value.t :=
    let? copy_value := Impl_Container.copy_value (Impl_ContainerRef.container self) in
    Result.Ok $ ValueImpl.Container copy_value.

  (*
  fn write_ref(self, v: Value) -> PartialVMResult<()> {
    match v.0 {
        ValueImpl::Container(c) => {
            macro_rules! assign {
                ($r1: expr, $tc: ident) => {{
                    let r = match c {
                        Container::$tc(v) => v,
                        _ => {
                            return Err(PartialVMError::new(
                                StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR,
                            )
                            .with_message(
                              "failed to write_ref: container type mismatch".to_string(),
                              ))
                          }
                      };
                      *$r1.borrow_mut() = take_unique_ownership(r)?;
                  }};
              }

              match self.container() {
                  Container::Struct(r) => assign!(r, Struct),
                  Container::Vec(r) => assign!(r, Vec),
                  Container::VecU8(r) => assign!(r, VecU8),
                  Container::VecU16(r) => assign!(r, VecU16),
                  Container::VecU32(r) => assign!(r, VecU32),
                  Container::VecU64(r) => assign!(r, VecU64),
                  Container::VecU128(r) => assign!(r, VecU128),
                  Container::VecU256(r) => assign!(r, VecU256),
                  Container::VecBool(r) => assign!(r, VecBool),
                  Container::VecAddress(r) => assign!(r, VecAddress),
                  Container::Locals(_) => {
                      return Err(PartialVMError::new(
                          StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR,
                      )
                      .with_message("cannot overwrite Container::Locals".to_string()))
                  }
              }
              self.mark_dirty();
          }
          _ => {
              return Err(
                  PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
                      .with_message(format!(
                          "cannot write value {:?} to container ref {:?}",
                          v, self
                      )),
              )
          }
      }
      Ok(())
  }
  *)
  Definition write_ref (self : Self) (v : Value.t) : PartialVMResult.t unit. Admitted.
End Impl_ContainerRef'.

Module Impl_IndexedRef'.
  Definition Self := IndexedRef.t.

  (*
  fn read_ref(self) -> PartialVMResult<Value> {
      use Container::*;

      let res = match self.container_ref.container() {
          Locals(r) | Vec(r) | Struct(r) => r.borrow()[self.idx].copy_value()?,
          VecU8(r) => ValueImpl::U8(r.borrow()[self.idx]),
          VecU16(r) => ValueImpl::U16(r.borrow()[self.idx]),
          VecU32(r) => ValueImpl::U32(r.borrow()[self.idx]),
          VecU64(r) => ValueImpl::U64(r.borrow()[self.idx]),
          VecU128(r) => ValueImpl::U128(r.borrow()[self.idx]),
          VecU256(r) => ValueImpl::U256(r.borrow()[self.idx]),
          VecBool(r) => ValueImpl::Bool(r.borrow()[self.idx]),
          VecAddress(r) => ValueImpl::Address(r.borrow()[self.idx]),
      };

      Ok(Value(res))
  }
  *)
  Definition read_ref (self : Self) : M! (PartialVMResult.t Value.t) :=
    match Impl_ContainerRef.container self.(IndexedRefSkeleton.container_ref) with
    | ContainerSkeleton.Locals r
    | ContainerSkeleton.Vec r
    | ContainerSkeleton.Struct r =>
      let! v := Panic.List.nth r (Z.to_nat self.(IndexedRefSkeleton.idx)) in
      return! $ Impl_ValueImpl.copy_value v
    | ContainerSkeleton.VecU8 r =>
      let! v := Panic.List.nth r (Z.to_nat self.(IndexedRefSkeleton.idx)) in
      return!? $ ValueImpl.U8 v
    | ContainerSkeleton.VecU16 r =>
      let! v := Panic.List.nth r (Z.to_nat self.(IndexedRefSkeleton.idx)) in
      return!? $ ValueImpl.U16 v
    | ContainerSkeleton.VecU32 r =>
      let! v := Panic.List.nth r (Z.to_nat self.(IndexedRefSkeleton.idx)) in
      return!? $ ValueImpl.U32 v
    | ContainerSkeleton.VecU64 r =>
      let! v := Panic.List.nth r (Z.to_nat self.(IndexedRefSkeleton.idx)) in
      return!? $ ValueImpl.U64 v
    | ContainerSkeleton.VecU128 r =>
      let! v := Panic.List.nth r (Z.to_nat self.(IndexedRefSkeleton.idx)) in
      return!? $ ValueImpl.U128 v
    | ContainerSkeleton.VecU256 r =>
      let! v := Panic.List.nth r (Z.to_nat self.(IndexedRefSkeleton.idx)) in
      return!? $ ValueImpl.U256 v
    | ContainerSkeleton.VecBool r =>
      let! v := Panic.List.nth r (Z.to_nat self.(IndexedRefSkeleton.idx)) in
      return!? $ ValueImpl.Bool v
    | ContainerSkeleton.VecAddress r =>
      let! v := Panic.List.nth r (Z.to_nat self.(IndexedRefSkeleton.idx)) in
      return!? $ ValueImpl.Address v
    end.

  (*
  fn write_ref(self, x: Value) -> PartialVMResult<()> {
        match &x.0 {
            ValueImpl::IndexedRef(_)
            | ValueImpl::ContainerRef(_)
            | ValueImpl::Invalid
            | ValueImpl::Container(_) => {
                return Err(
                    PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
                        .with_message(format!(
                          "cannot write value {:?} to indexed ref {:?}",
                          x, self
                      )),
              )
          }
          _ => (),
      }

      match (self.container_ref.container(), &x.0) {
          (Container::Locals(r), _) | (Container::Vec(r), _) | (Container::Struct(r), _) => {
              let mut v = r.borrow_mut();
              v[self.idx] = x.0;
          }
          (Container::VecU8(r), ValueImpl::U8(x)) => r.borrow_mut()[self.idx] = *x,
          (Container::VecU16(r), ValueImpl::U16(x)) => r.borrow_mut()[self.idx] = *x,
          (Container::VecU32(r), ValueImpl::U32(x)) => r.borrow_mut()[self.idx] = *x,
          (Container::VecU64(r), ValueImpl::U64(x)) => r.borrow_mut()[self.idx] = *x,
          (Container::VecU128(r), ValueImpl::U128(x)) => r.borrow_mut()[self.idx] = *x,
          (Container::VecU256(r), ValueImpl::U256(x)) => r.borrow_mut()[self.idx] = *x,
          (Container::VecBool(r), ValueImpl::Bool(x)) => r.borrow_mut()[self.idx] = *x,
          (Container::VecAddress(r), ValueImpl::Address(x)) => r.borrow_mut()[self.idx] = *x,

          (Container::VecU8(_), _)
          | (Container::VecU16(_), _)
          | (Container::VecU32(_), _)
          | (Container::VecU64(_), _)
          | (Container::VecU128(_), _)
          | (Container::VecU256(_), _)
          | (Container::VecBool(_), _)
          | (Container::VecAddress(_), _) => {
              return Err(
                  PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
                      "cannot write value {:?} to indexed ref {:?}",
                      x, self
                  )),
              )
          }
      }
      self.container_ref.mark_dirty();
      Ok(())
  }
  *)
  Definition write_ref (self : Self) (x : Value.t) : PartialVMResult.t unit. Admitted.
End Impl_IndexedRef'.

Module Impl_ReferenceImpl.
  Definition Self := ReferenceImpl.t.

  (*
  fn read_ref(self) -> PartialVMResult<Value> {
      match self {
          Self::ContainerRef(r) => r.read_ref(),
          Self::IndexedRef(r) => r.read_ref(),
      }
  }
  *)
  Definition read_ref (self : Self) : M! (PartialVMResult.t Value.t) :=
    match self with
    | ReferenceImpl.ContainerRef r => return! $ Impl_ContainerRef'.read_ref r
    | ReferenceImpl.IndexedRef r => Impl_IndexedRef'.read_ref r
    end.

  (*
  fn write_ref(self, x: Value) -> PartialVMResult<()> {
      match self {
          Self::ContainerRef(r) => r.write_ref(x),
          Self::IndexedRef(r) => r.write_ref(x),
      }
  }
  *)
  Definition write_ref (self : Self) (x : Value.t) : PartialVMResult.t unit :=
    match self with
    | ReferenceImpl.ContainerRef r => Impl_ContainerRef'.write_ref r x
    | ReferenceImpl.IndexedRef r => Impl_IndexedRef'.write_ref r x
    end.
End Impl_ReferenceImpl.

(*
#[derive(Debug)]
pub struct Struct {
    fields: Vec<ValueImpl>,
}
*)

Module Struct.
  Record t : Set := {
    fields : list ValueImpl.t;
  }.
End Struct.

Module Impl_Struct.

  (* 
  pub fn pack<I: IntoIterator<Item = Value>>(vals: I) -> Self {
      Self {
          fields: vals.into_iter().map(|v| v.0).collect(),
      }
  }
  *)
  Definition pack (vals : list Value.t) : Struct.t :=
    {|
      Struct.fields := vals;
    |}.

  (*
  pub fn unpack(self) -> PartialVMResult<impl Iterator<Item = Value>> {
      Ok(self.fields.into_iter().map(Value))
  }
  *)
  Definition unpack (self : Struct.t) : PartialVMResult.t (list Value.t) :=
    Result.Ok self.(Struct.fields).
End Impl_Struct.

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
End Locals.

Module Impl_Locals.
  Definition Self := move_sui.simulations.move_vm_types.values.values_impl.Locals.t.

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
    match List.nth_error self (Z.to_nat idx) with
    | Some value =>
      let is_invalid :=
        match value with
        | ValueImpl.Invalid => true
        | _ => false
        end in
      if is_invalid then
        Result.Err $ PartialVMError.new StatusCode.UNKNOWN_INVARIANT_VIOLATION_ERROR
      else
        Impl_ValueImpl.copy_value value
    | None => Result.Err $ PartialVMError.new StatusCode.VERIFIER_INVARIANT_VIOLATION
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

  Definition swap_loc (idx : Z) (x : Value.t) (violation_check : bool) :
      MS! Self (PartialVMResult.t Value.t).
  Admitted.
    (* if Z.of_nat $ List.length v <=? idx then
      returnS! $ Result.Err $ PartialVMError.new StatusCode.VERIFIER_INVARIANT_VIOLATION
    else
      let v_nth := List.nth (Z.to_nat idx) v default_valueimpl in
      if violation_check then
        (* NOTE: we ignore the case where rc_counter is greater than 1. Might find a way to deal
            with it in the future *)
        let v_new := swap_list_nth v x (Z.to_nat idx) in
        letS! _ := writeS! (v_new, v_nth) in
          returnS! $ Result.Ok $ v_nth
      else
        returnS! $ Result.Err $ PartialVMError.new StatusCode.VERIFIER_INVARIANT_VIOLATION. *)

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
    letS!? result := swap_loc idx ValueImpl.Invalid violation_check in
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
  Definition store_loc (idx : Z) (x : Value.t) (violation_check : bool) 
    : MS! Self (PartialVMResult.t unit) :=
    letS!? result := swap_loc idx x violation_check in
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

Module IntegerValue.
  Inductive t : Set :=
  | U8 : Z -> t
  | U16 : Z -> t
  | U32 : Z -> t
  | U64 : Z -> t
  | U128 : Z -> t
  | U256 : Z -> t
  .

  (** This function is not in the original Rust code but is convenient for the proofs. *)
  Definition to_value_impl (self : t) : ValueImpl.t :=
    match self with
    | U8 x => ValueImpl.U8 x
    | U16 x => ValueImpl.U16 x
    | U32 x => ValueImpl.U32 x
    | U64 x => ValueImpl.U64 x
    | U128 x => ValueImpl.U128 x
    | U256 x => ValueImpl.U256 x
    end.

  Definition checked_add (a : IntegerValue.t) (b : IntegerValue.t) : option IntegerValue.t :=
    match a, b with
    | IntegerValue.U8 l, IntegerValue.U8 r =>
      if l + r <=? 2^8 - 1
      then Some (IntegerValue.U8 (l + r))
      else None
    | IntegerValue.U16 l, IntegerValue.U16 r =>
      if l + r <=? 2^16 - 1
      then Some (IntegerValue.U16 (l + r))
      else None
    | IntegerValue.U32 l, IntegerValue.U32 r =>
      if l + r <=? 2^32 - 1
      then Some (IntegerValue.U32 (l + r))
      else None
    | IntegerValue.U64 l, IntegerValue.U64 r =>
      if l + r <=? 2^64 - 1
      then Some (IntegerValue.U64 (l + r))
      else None
    | IntegerValue.U128 l, IntegerValue.U128 r =>
      if l + r <=? 2^128 - 1
      then Some (IntegerValue.U128 (l + r))
      else None
    | IntegerValue.U256 l, IntegerValue.U256 r =>
      if l + r <=? 2^256 - 1
      then Some (IntegerValue.U256 (l + r))
      else None
    | _, _ => None
    end.

  Definition checked_sub (a : IntegerValue.t) (b : IntegerValue.t) : option IntegerValue.t :=
    match a, b with
    | IntegerValue.U8 l, IntegerValue.U8 r =>
      if l >=? r
      then Some (IntegerValue.U8 (l - r))
      else None
    | IntegerValue.U16 l, IntegerValue.U16 r =>
      if l >=? r
      then Some (IntegerValue.U16 (l - r))
      else None
    | IntegerValue.U32 l, IntegerValue.U32 r =>
      if l >=? r
      then Some (IntegerValue.U32 (l - r))
      else None
    | IntegerValue.U64 l, IntegerValue.U64 r =>
      if l >=? r
      then Some (IntegerValue.U64 (l - r))
      else None
    | IntegerValue.U128 l, IntegerValue.U128 r =>
      if l >=? r
      then Some (IntegerValue.U128 (l - r))
      else None
    | IntegerValue.U256 l, IntegerValue.U256 r =>
      if l >=? r
      then Some (IntegerValue.U256 (l - r))
      else None
    | _, _ => None
    end.

  Definition checked_mul (a : IntegerValue.t) (b : IntegerValue.t) : option IntegerValue.t :=
    match a, b with
    | IntegerValue.U8 l, IntegerValue.U8 r =>
      if l * r <=? 2^8 - 1
      then Some (IntegerValue.U8 (l * r))
      else None
    | IntegerValue.U16 l, IntegerValue.U16 r =>
      if l * r <=? 2^16 - 1
      then Some (IntegerValue.U16 (l * r))
      else None
    | IntegerValue.U32 l, IntegerValue.U32 r =>
      if l * r <=? 2^32 - 1
      then Some (IntegerValue.U32 (l * r))
      else None
    | IntegerValue.U64 l, IntegerValue.U64 r =>
      if l * r <=? 2^64 - 1
      then Some (IntegerValue.U64 (l * r))
      else None
    | IntegerValue.U128 l, IntegerValue.U128 r =>
      if l * r <=? 2^128 - 1
      then Some (IntegerValue.U128 (l * r))
      else None
    | IntegerValue.U256 l, IntegerValue.U256 r =>
      if l * r <=? 2^256 - 1
      then Some (IntegerValue.U256 (l * r))
      else None
    | _, _ => None
    end.

  Definition checked_div (a : IntegerValue.t) (b : IntegerValue.t) : option IntegerValue.t :=
    match a, b with
    | IntegerValue.U8 l, IntegerValue.U8 r =>
      if r =? 0
      then None
      else Some (IntegerValue.U8 (l / r))
    | IntegerValue.U16 l, IntegerValue.U16 r =>
      if r =? 0
      then None
      else Some (IntegerValue.U16 (l / r))
    | IntegerValue.U32 l, IntegerValue.U32 r =>
      if r =? 0
      then None
      else Some (IntegerValue.U32 (l / r))
    | IntegerValue.U64 l, IntegerValue.U64 r =>
      if r =? 0
      then None
      else Some (IntegerValue.U64 (l / r))
    | IntegerValue.U128 l, IntegerValue.U128 r =>
      if r =? 0
      then None
      else Some (IntegerValue.U128 (l / r))
    | IntegerValue.U256 l, IntegerValue.U256 r =>
      if r =? 0
      then None
      else Some (IntegerValue.U256 (l / r))
    | _, _ => None
    end.

  Definition checked_rem (a : IntegerValue.t) (b : IntegerValue.t) : option IntegerValue.t :=
  match a, b with
  | IntegerValue.U8 l, IntegerValue.U8 r =>
    if r =? 0
    then None
    else Some (IntegerValue.U8 (l mod r))
  | IntegerValue.U16 l, IntegerValue.U16 r =>
    if r =? 0
    then None
    else Some (IntegerValue.U16 (l mod r))
  | IntegerValue.U32 l, IntegerValue.U32 r =>
    if r =? 0
    then None
    else Some (IntegerValue.U32 (l mod r))
  | IntegerValue.U64 l, IntegerValue.U64 r =>
    if r =? 0
    then None
    else Some (IntegerValue.U64 (l mod r))
  | IntegerValue.U128 l, IntegerValue.U128 r =>
    if r =? 0
    then None
    else Some (IntegerValue.U128 (l mod r))
  | IntegerValue.U256 l, IntegerValue.U256 r =>
    if r =? 0
    then None
    else Some (IntegerValue.U256 (l mod r))
  | _, _ => None
  end.

 Definition bit_or (a : IntegerValue.t) (b : IntegerValue.t) : PartialVMResult.t IntegerValue.t :=
  match a, b with
  | IntegerValue.U8 l, IntegerValue.U8 r => 
      Result.Ok (IntegerValue.U8 (Z.lor l r))
  | IntegerValue.U16 l, IntegerValue.U16 r =>
      Result.Ok (IntegerValue.U16 (Z.lor l r))
  | IntegerValue.U32 l, IntegerValue.U32 r =>
      Result.Ok (IntegerValue.U32 (Z.lor l r))
  | IntegerValue.U64 l, IntegerValue.U64 r =>
      Result.Ok (IntegerValue.U64 (Z.lor l r))
  | IntegerValue.U128 l, IntegerValue.U128 r =>
      Result.Ok (IntegerValue.U128 (Z.lor l r))
  | IntegerValue.U256 l, IntegerValue.U256 r =>
      Result.Ok (IntegerValue.U256 (Z.lor l r))
  | _, _ =>
      Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  end.

  Definition bit_and (a : IntegerValue.t) (b : IntegerValue.t) : PartialVMResult.t IntegerValue.t :=
  match a, b with
  | IntegerValue.U8 l, IntegerValue.U8 r => 
      Result.Ok (IntegerValue.U8 (Z.land l r))
  | IntegerValue.U16 l, IntegerValue.U16 r =>
      Result.Ok (IntegerValue.U16 (Z.land l r))
  | IntegerValue.U32 l, IntegerValue.U32 r =>
      Result.Ok (IntegerValue.U32 (Z.land l r))
  | IntegerValue.U64 l, IntegerValue.U64 r =>
      Result.Ok (IntegerValue.U64 (Z.land l r))
  | IntegerValue.U128 l, IntegerValue.U128 r =>
      Result.Ok (IntegerValue.U128 (Z.land l r))
  | IntegerValue.U256 l, IntegerValue.U256 r =>
      Result.Ok (IntegerValue.U256 (Z.land l r))
  | _, _ =>
      Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  end.

  Definition bit_xor (a : IntegerValue.t) (b : IntegerValue.t) : PartialVMResult.t IntegerValue.t :=
  match a, b with
  | IntegerValue.U8 l, IntegerValue.U8 r => 
      Result.Ok (IntegerValue.U8 (Z.lxor l r))
  | IntegerValue.U16 l, IntegerValue.U16 r =>
      Result.Ok (IntegerValue.U16 (Z.lxor l r))
  | IntegerValue.U32 l, IntegerValue.U32 r =>
      Result.Ok (IntegerValue.U32 (Z.lxor l r))
  | IntegerValue.U64 l, IntegerValue.U64 r =>
      Result.Ok (IntegerValue.U64 (Z.lxor l r))
  | IntegerValue.U128 l, IntegerValue.U128 r =>
      Result.Ok (IntegerValue.U128 (Z.lxor l r))
  | IntegerValue.U256 l, IntegerValue.U256 r =>
      Result.Ok (IntegerValue.U256 (Z.lxor l r))
  | _, _ =>
      Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  end.

  Definition add_checked (self : IntegerValue.t) (other : IntegerValue.t) : PartialVMResult.t IntegerValue.t :=
    match checked_add self other with
    | Some res => Result.Ok res
    | None => Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    end.

  Definition sub_checked (self : IntegerValue.t) (other : IntegerValue.t) : PartialVMResult.t IntegerValue.t :=
    match checked_sub self other with
    | Some res => Result.Ok res
    | None => Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    end.

  Definition mul_checked (self : IntegerValue.t) (other : IntegerValue.t) : PartialVMResult.t IntegerValue.t :=
    match checked_mul self other with
    | Some res => Result.Ok res
    | None => Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    end.

  Definition div_checked (self : IntegerValue.t) (other : IntegerValue.t) : PartialVMResult.t IntegerValue.t :=
    match checked_div self other with
    | Some res => Result.Ok res
    | None => Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    end.

  Definition rem_checked (self : IntegerValue.t) (other : IntegerValue.t) : PartialVMResult.t IntegerValue.t :=
    match checked_rem self other with
    | Some res => Result.Ok res
    | None => Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    end.

  Definition shl_checked (self : IntegerValue.t) (nbits : U8.t) : PartialVMResult.t IntegerValue.t :=
    let r : Z := nbits.(Integer.value) in
    match self with
    | IntegerValue.U8 l =>
      if r <? 8
      then Result.Ok (IntegerValue.U8 (Z.shiftl l r))
      else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    | IntegerValue.U16 l =>
      if r <? 16
      then Result.Ok (IntegerValue.U16 (Z.shiftl l r))
      else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    | IntegerValue.U32 l =>
      if r <? 32
      then Result.Ok (IntegerValue.U32 (Z.shiftl l r))
      else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    | IntegerValue.U64 l =>
      if r <? 64
      then Result.Ok (IntegerValue.U64 (Z.shiftl l r))
      else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    | IntegerValue.U128 l =>
      if r <? 128
      then Result.Ok (IntegerValue.U128 (Z.shiftl l r))
      else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    | IntegerValue.U256 l =>
      if r <? 256
      then Result.Ok (IntegerValue.U256 (Z.shiftl l r))
      else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    end.

  Definition shr_checked (self : IntegerValue.t) (nbits : U8.t) : PartialVMResult.t IntegerValue.t :=
    let r : Z := nbits.(Integer.value) in
    match self with
    | IntegerValue.U8 l =>
      if r <? 8
      then Result.Ok (IntegerValue.U8 (Z.shiftr l r))
      else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    | IntegerValue.U16 l =>
      if r <? 16
      then Result.Ok (IntegerValue.U16 (Z.shiftr l r))
      else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    | IntegerValue.U32 l =>
      if r <? 32
      then Result.Ok (IntegerValue.U32 (Z.shiftr l r))
      else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    | IntegerValue.U64 l =>
      if r <? 64
      then Result.Ok (IntegerValue.U64 (Z.shiftr l r))
      else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    | IntegerValue.U128 l =>
      if r <? 128
      then Result.Ok (IntegerValue.U128 (Z.shiftr l r))
      else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    | IntegerValue.U256 l =>
      if r <? 256
      then Result.Ok (IntegerValue.U256 (Z.shiftr l r))
      else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
    end.

  Definition lt (self : IntegerValue.t) (other : IntegerValue.t) : PartialVMResult.t bool :=
  match self, other with
  | IntegerValue.U8 l, IntegerValue.U8 r => Result.Ok (l <? r)
  | IntegerValue.U16 l, IntegerValue.U16 r => Result.Ok (l <? r)
  | IntegerValue.U32 l, IntegerValue.U32 r => Result.Ok (l <? r)
  | IntegerValue.U64 l, IntegerValue.U64 r => Result.Ok (l <? r)
  | IntegerValue.U128 l, IntegerValue.U128 r => Result.Ok (l <? r)
  | IntegerValue.U256 l, IntegerValue.U256 r => Result.Ok (l <? r)
  | _, _ => Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  end.

  Definition le (self : IntegerValue.t) (other : IntegerValue.t) : PartialVMResult.t bool :=
  match self, other with
  | IntegerValue.U8 l, IntegerValue.U8 r => Result.Ok (l <=? r)
  | IntegerValue.U16 l, IntegerValue.U16 r => Result.Ok (l <=? r)
  | IntegerValue.U32 l, IntegerValue.U32 r => Result.Ok (l <=? r)
  | IntegerValue.U64 l, IntegerValue.U64 r => Result.Ok (l <=? r)
  | IntegerValue.U128 l, IntegerValue.U128 r => Result.Ok (l <=? r)
  | IntegerValue.U256 l, IntegerValue.U256 r => Result.Ok (l <=? r)
  | _, _ => Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  end.

  Definition gt (self : IntegerValue.t) (other : IntegerValue.t) : PartialVMResult.t bool :=
  match self, other with
  | IntegerValue.U8 l, IntegerValue.U8 r => Result.Ok (l >? r)
  | IntegerValue.U16 l, IntegerValue.U16 r => Result.Ok (l >? r)
  | IntegerValue.U32 l, IntegerValue.U32 r => Result.Ok (l >? r)
  | IntegerValue.U64 l, IntegerValue.U64 r => Result.Ok (l >? r)
  | IntegerValue.U128 l, IntegerValue.U128 r => Result.Ok (l >? r)
  | IntegerValue.U256 l, IntegerValue.U256 r => Result.Ok (l >? r)
  | _, _ => Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  end.

  Definition ge (self : IntegerValue.t) (other : IntegerValue.t) : PartialVMResult.t bool :=
  match self, other with
  | IntegerValue.U8 l, IntegerValue.U8 r => Result.Ok (l >=? r)
  | IntegerValue.U16 l, IntegerValue.U16 r => Result.Ok (l >=? r)
  | IntegerValue.U32 l, IntegerValue.U32 r => Result.Ok (l >=? r)
  | IntegerValue.U64 l, IntegerValue.U64 r => Result.Ok (l >=? r)
  | IntegerValue.U128 l, IntegerValue.U128 r => Result.Ok (l >=? r)
  | IntegerValue.U256 l, IntegerValue.U256 r => Result.Ok (l >=? r)
  | _, _ => Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  end.

  Definition cast_u8 (self : IntegerValue.t) : PartialVMResult.t Z :=
  match self with
  | IntegerValue.U8 l => Result.Ok l
  | IntegerValue.U16 l => if l <=? 2^8 - 1
    then Result.Ok l
    else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  | IntegerValue.U32 l => if l <=? 2^8 - 1
    then Result.Ok l
    else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  | IntegerValue.U64 l => if l <=? 2^8 - 1
    then Result.Ok l
    else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  | IntegerValue.U128 l => if l <=? 2^8 - 1
    then Result.Ok l
    else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  | IntegerValue.U256 l => if l <=? 2^8 - 1
    then Result.Ok l
    else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  end.

Definition cast_u16 (self : IntegerValue.t) : PartialVMResult.t Z :=
  match self with
  | IntegerValue.U8 l => Result.Ok l
  | IntegerValue.U16 l => Result.Ok l
  | IntegerValue.U32 l => if l <=? 2^16 - 1
    then Result.Ok l
    else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  | IntegerValue.U64 l => if l <=? 2^16 - 1
    then Result.Ok l
    else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  | IntegerValue.U128 l => if l <=? 2^16 - 1
    then Result.Ok l
    else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  | IntegerValue.U256 l => if l <=? 2^16 - 1
    then Result.Ok l
    else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  end.

Definition cast_u32 (self : IntegerValue.t) : PartialVMResult.t Z :=
  match self with
  | IntegerValue.U8 l => Result.Ok l
  | IntegerValue.U16 l => Result.Ok l
  | IntegerValue.U32 l => Result.Ok l
  | IntegerValue.U64 l => if l <=? 2^32 - 1
    then Result.Ok l
    else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  | IntegerValue.U128 l => if l <=? 2^32 - 1
    then Result.Ok l
    else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  | IntegerValue.U256 l => if l <=? 2^32 - 1
    then Result.Ok l
    else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  end.

Definition cast_u64 (self : IntegerValue.t) : PartialVMResult.t Z :=
  match self with
  | IntegerValue.U8 l => Result.Ok l
  | IntegerValue.U16 l => Result.Ok l
  | IntegerValue.U32 l => Result.Ok l
  | IntegerValue.U64 l => Result.Ok l
  | IntegerValue.U128 l => if l <=? 2^64 - 1
    then Result.Ok l
    else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  | IntegerValue.U256 l => if l <=? 2^64 - 1
    then Result.Ok l
    else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  end.

Definition cast_u128 (self : IntegerValue.t) : PartialVMResult.t Z :=
  match self with
  | IntegerValue.U8 l => Result.Ok l
  | IntegerValue.U16 l => Result.Ok l
  | IntegerValue.U32 l => Result.Ok l
  | IntegerValue.U64 l => Result.Ok l
  | IntegerValue.U128 l => Result.Ok l
  | IntegerValue.U256 l => if l <=? 2^128 - 1
    then Result.Ok l
    else Result.Err (PartialVMError.new StatusCode.ARITHMETIC_ERROR)
  end.

Definition cast_u256 (self : IntegerValue.t) : PartialVMResult.t Z :=
  match self with
  | IntegerValue.U8 l => Result.Ok l
  | IntegerValue.U16 l => Result.Ok l
  | IntegerValue.U32 l => Result.Ok l
  | IntegerValue.U64 l => Result.Ok l
  | IntegerValue.U128 l => Result.Ok l
  | IntegerValue.U256 l => Result.Ok l
  end.

  (*
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
  *)
  Definition into_value (self : IntegerValue.t) : Value.t :=
    match self with
    | IntegerValue.U8 x => ValueImpl.U8 x
    | IntegerValue.U16 x => ValueImpl.U16 x
    | IntegerValue.U32 x => ValueImpl.U32 x
    | IntegerValue.U64 x => ValueImpl.U64 x
    | IntegerValue.U128 x => ValueImpl.U128 x
    | IntegerValue.U256 x => ValueImpl.U256 x
    end.
End IntegerValue.
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

(*
impl VMValueCast<IntegerValue> for Value {
    fn cast(self) -> PartialVMResult<IntegerValue> {
        match self.0 {
            ValueImpl::U8(x) => Ok(IntegerValue::U8(x)),
            ValueImpl::U16(x) => Ok(IntegerValue::U16(x)),
            ValueImpl::U32(x) => Ok(IntegerValue::U32(x)),
            ValueImpl::U64(x) => Ok(IntegerValue::U64(x)),
            ValueImpl::U128(x) => Ok(IntegerValue::U128(x)),
            ValueImpl::U256(x) => Ok(IntegerValue::U256(x)),
            v => Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
                .with_message(format!("cannot cast {:?} to integer", v,))),
        }
    }
}
*)

Global Instance Impl_VMValueCast_IntegerValue_for_Value :
    VMValueCast.Trait Value.t IntegerValue.t : Set := {
  cast self :=
    match self with
    | ValueImpl.U8 x => return? $ IntegerValue.U8 x
    | ValueImpl.U16 x => return? $ IntegerValue.U16 x
    | ValueImpl.U32 x => return? $ IntegerValue.U32 x
    | ValueImpl.U64 x => return? $ IntegerValue.U64 x
    | ValueImpl.U128 x => return? $ IntegerValue.U128 x
    | ValueImpl.U256 x => return? $ IntegerValue.U256 x
    | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
    end;
}.

(*
fn take_unique_ownership<T: Debug>(r: Rc<RefCell<T>>) -> PartialVMResult<T> {
    match Rc::try_unwrap(r) {
        Ok(cell) => Ok(cell.into_inner()),
        Err(r) => Err(
            PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
                .with_message(format!("moving value {:?} with dangling references", r)),
        ),
    }
*)

Definition take_unique_ownership {T : Set} (refCell : T) : PartialVMResult.t T :=
  Result.Ok refCell.

(*
?H: Cannot infer the implicit parameter H of Stack.Impl_Stack.pop_as
whose type is "VMValueCast.Trait Value.t Struct.t" (no type class
instance found) in environment:
*)
(*
impl VMValueCast<Struct> for Value {
    fn cast(self) -> PartialVMResult<Struct> {
        match self.0 {
            ValueImpl::Container(Container::Struct(r)) => Ok(Struct {
                fields: take_unique_ownership(r)?,
            }),
            v => Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
                .with_message(format!("cannot cast {:?} to struct", v,))),
        }
    }
}
*)

(* 
Global Instance Impl_VMValueCast_Struct_for_Value : VMValueCast.Trait Value.t Struct.t : Set := {
  cast self :=
    match self with
    | ValueImpl.Container (Container.Struct r) =>
      match take_unique_ownership r with
      | Result.Ok inner_r => Result.Ok (Struct.Build_t (map Value.coerce_Container_Locals inner_r))
      | Result.Err e => Result.Err e
      end
    | _ => Result.Err $ PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR
    end;
}.
*)

(*
?H: Cannot infer the implicit parameter H of Stack.Impl_Stack.pop_as whose
type is "VMValueCast.Trait Value.t Reference.t" (no type class instance
found) in environment:
*)

(*
impl VMValueCast<Reference> for Value {
  fn cast(self) -> PartialVMResult<Reference> {
    match self.0 {
      ValueImpl::ContainerRef(r) => Ok(Reference(ReferenceImpl::ContainerRef(r))),
      ValueImpl::IndexedRef(r) => Ok(Reference(ReferenceImpl::IndexedRef(r))),
      v => Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
        .with_message(format!("cannot cast {:?} to reference", v,))),
    }
  }
}
*)

Global Instance Impl_VMValueCast_Reference_for_Value : VMValueCast.Trait Value.t Reference.t : Set := {
  cast self :=
  match self with
  | ValueImpl.ContainerRef r => Result.Ok (ReferenceImpl.ContainerRef r)
  | ValueImpl.IndexedRef r => Result.Ok (ReferenceImpl.IndexedRef r)
  | _ => Result.Err (PartialVMError.new StatusCode.INTERNAL_TYPE_ERROR)
  end;
}.
