(* Generated file for the links. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require links.alloc.alloc.
Require links.alloc.boxed.
Require links.alloc.vec.

Import Run.

Module AbilitySet.
  Inductive t : Set :=
  | Make : u8.t -> t.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::AbilitySet";
    to_value '(Make x0) :=
      Value.StructTuple "move_binary_format::file_format::AbilitySet" [to_value x0];
  }.
End AbilitySet.

Module StructTypeParameter.
  Record t : Set := {
    constraints: move_binary_format.file_format.AbilitySet.t;
    is_phantom: bool;
  }.

  Definition current_to_value (x: t) : Value.t :=
    match x with
    | Build_t constraints is_phantom =>
      Value.StructRecord "move_binary_format::file_format::StructTypeParameter" [
        ("constraints", to_value constraints);
        ("is_phantom", to_value is_phantom)
      ]
    end.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::StructTypeParameter";
    to_value := to_value
  }.
End StructTypeParameter.

Module ModuleHandleIndex.
  Inductive t : Set :=
  | Make : u16.t -> t.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::ModuleHandleIndex";
    to_value '(Make x0) :=
      Value.StructTuple "move_binary_format::file_format::ModuleHandleIndex" [to_value x0];
  }.
End ModuleHandleIndex.

Module AddressIdentifierIndex.
  Inductive t : Set :=
  | Make : u16.t -> t.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::AddressIdentifierIndex";
    to_value '(Make x0) :=
      Value.StructTuple "move_binary_format::file_format::AddressIdentifierIndex" [to_value x0];
  }.
End AddressIdentifierIndex.

Module IdentifierIndex.
  Inductive t : Set :=
  | Make : u16.t -> t.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::IdentifierIndex";
    to_value '(Make x0) :=
      Value.StructTuple "move_binary_format::file_format::IdentifierIndex" [to_value x0];
  }.
End IdentifierIndex.

Module ModuleHandle.
  Record t : Set := {
    address: move_binary_format.file_format.AddressIdentifierIndex.t;
    name: move_binary_format.file_format.IdentifierIndex.t;
  }.

  Definition current_to_value (x: t) : Value.t :=
    match x with
    | Build_t address name =>
      Value.StructRecord "move_binary_format::file_format::ModuleHandle" [
        ("address", to_value address);
        ("name", to_value name)
      ]
    end.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::ModuleHandle";
    to_value := to_value
  }.
End ModuleHandle.

Module StructHandle.
  Record t : Set := {
    module: move_binary_format.file_format.ModuleHandleIndex.t;
    name: move_binary_format.file_format.IdentifierIndex.t;
    abilities: move_binary_format.file_format.AbilitySet.t;
    type_parameters: alloc.vec.Vec.t move_binary_format.file_format.StructTypeParameter.t alloc.alloc.Global.t;
  }.

  Definition current_to_value (x: t) : Value.t :=
    match x with
    | Build_t module name abilities type_parameters =>
      Value.StructRecord "move_binary_format::file_format::StructHandle" [
        ("module", to_value module);
        ("name", to_value name);
        ("abilities", to_value abilities);
        ("type_parameters", to_value type_parameters)
      ]
    end.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::StructHandle";
    to_value := to_value
  }.
End StructHandle.

Module SignatureIndex.
  Inductive t : Set :=
  | Make : u16.t -> t.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::SignatureIndex";
    to_value '(Make x0) :=
      Value.StructTuple "move_binary_format::file_format::SignatureIndex" [to_value x0];
  }.
End SignatureIndex.

Module FunctionHandle.
  Record t : Set := {
    module: move_binary_format.file_format.ModuleHandleIndex.t;
    name: move_binary_format.file_format.IdentifierIndex.t;
    parameters: move_binary_format.file_format.SignatureIndex.t;
    return_: move_binary_format.file_format.SignatureIndex.t;
    type_parameters: alloc.vec.Vec.t move_binary_format.file_format.AbilitySet.t alloc.alloc.Global.t;
  }.

  Definition current_to_value (x: t) : Value.t :=
    match x with
    | Build_t module name parameters return_ type_parameters =>
      Value.StructRecord "move_binary_format::file_format::FunctionHandle" [
        ("module", to_value module);
        ("name", to_value name);
        ("parameters", to_value parameters);
        ("return_", to_value return_);
        ("type_parameters", to_value type_parameters)
      ]
    end.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::FunctionHandle";
    to_value := to_value
  }.
End FunctionHandle.

Module StructDefinitionIndex.
  Inductive t : Set :=
  | Make : u16.t -> t.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::StructDefinitionIndex";
    to_value '(Make x0) :=
      Value.StructTuple "move_binary_format::file_format::StructDefinitionIndex" [to_value x0];
  }.
End StructDefinitionIndex.

Module FieldHandle.
  Record t : Set := {
    owner: move_binary_format.file_format.StructDefinitionIndex.t;
    field: u16.t;
  }.

  Definition current_to_value (x: t) : Value.t :=
    match x with
    | Build_t owner field =>
      Value.StructRecord "move_binary_format::file_format::FieldHandle" [
        ("owner", to_value owner);
        ("field", to_value field)
      ]
    end.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::FieldHandle";
    to_value := to_value
  }.
End FieldHandle.

Module StructDefInstantiation.
  Record t : Set := {
    def: move_binary_format.file_format.StructDefinitionIndex.t;
    type_parameters: move_binary_format.file_format.SignatureIndex.t;
  }.

  Definition current_to_value (x: t) : Value.t :=
    match x with
    | Build_t def type_parameters =>
      Value.StructRecord "move_binary_format::file_format::StructDefInstantiation" [
        ("def", to_value def);
        ("type_parameters", to_value type_parameters)
      ]
    end.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::StructDefInstantiation";
    to_value := to_value
  }.
End StructDefInstantiation.

Module FunctionHandleIndex.
  Inductive t : Set :=
  | Make : u16.t -> t.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::FunctionHandleIndex";
    to_value '(Make x0) :=
      Value.StructTuple "move_binary_format::file_format::FunctionHandleIndex" [to_value x0];
  }.
End FunctionHandleIndex.

Module FunctionInstantiation.
  Record t : Set := {
    handle: move_binary_format.file_format.FunctionHandleIndex.t;
    type_parameters: move_binary_format.file_format.SignatureIndex.t;
  }.

  Definition current_to_value (x: t) : Value.t :=
    match x with
    | Build_t handle type_parameters =>
      Value.StructRecord "move_binary_format::file_format::FunctionInstantiation" [
        ("handle", to_value handle);
        ("type_parameters", to_value type_parameters)
      ]
    end.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::FunctionInstantiation";
    to_value := to_value
  }.
End FunctionInstantiation.

Module FieldHandleIndex.
  Inductive t : Set :=
  | Make : u16.t -> t.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::FieldHandleIndex";
    to_value '(Make x0) :=
      Value.StructTuple "move_binary_format::file_format::FieldHandleIndex" [to_value x0];
  }.
End FieldHandleIndex.

Module FieldInstantiation.
  Record t : Set := {
    handle: move_binary_format.file_format.FieldHandleIndex.t;
    type_parameters: move_binary_format.file_format.SignatureIndex.t;
  }.

  Definition current_to_value (x: t) : Value.t :=
    match x with
    | Build_t handle type_parameters =>
      Value.StructRecord "move_binary_format::file_format::FieldInstantiation" [
        ("handle", to_value handle);
        ("type_parameters", to_value type_parameters)
      ]
    end.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::FieldInstantiation";
    to_value := to_value
  }.
End FieldInstantiation.

Module StructHandleIndex.
  Inductive t : Set :=
  | Make : u16.t -> t.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::StructHandleIndex";
    to_value '(Make x0) :=
      Value.StructTuple "move_binary_format::file_format::StructHandleIndex" [to_value x0];
  }.
End StructHandleIndex.

Module SignatureToken.
  #[bypass_check(positivity=yes)] Inductive t : Set :=
  | Bool
  | U8
  | U64
  | U128
  | Address
  | Signer
  | Vector : alloc.boxed.Box.t t alloc.alloc.Global.t -> t
  | Struct : move_binary_format.file_format.StructHandleIndex.t -> t
  | StructInstantiation : alloc.boxed.Box.t (move_binary_format.file_format.StructHandleIndex.t * (alloc.vec.Vec.t t alloc.alloc.Global.t)) alloc.alloc.Global.t -> t
  | Reference : alloc.boxed.Box.t t alloc.alloc.Global.t -> t
  | MutableReference : alloc.boxed.Box.t t alloc.alloc.Global.t -> t
  | TypeParameter : u16.t -> t
  | U16
  | U32
  | U256
  .

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::SignatureToken";
    to_value x :=
      match x with
      | Bool => Value.StructTuple "move_binary_format::file_format::SignatureToken::Bool" []
      | U8 => Value.StructTuple "move_binary_format::file_format::SignatureToken::U8" []
      | U64 => Value.StructTuple "move_binary_format::file_format::SignatureToken::U64" []
      | U128 => Value.StructTuple "move_binary_format::file_format::SignatureToken::U128" []
      | Address => Value.StructTuple "move_binary_format::file_format::SignatureToken::Address" []
      | Signer => Value.StructTuple "move_binary_format::file_format::SignatureToken::Signer" []
      | Vector  x0 => Value.StructTuple "move_binary_format::file_format::SignatureToken::Vector" [to_value x0]
      | Struct  x0 => Value.StructTuple "move_binary_format::file_format::SignatureToken::Struct" [to_value x0]
      | StructInstantiation  x0 => Value.StructTuple "move_binary_format::file_format::SignatureToken::StructInstantiation" [to_value x0]
      | Reference  x0 => Value.StructTuple "move_binary_format::file_format::SignatureToken::Reference" [to_value x0]
      | MutableReference  x0 => Value.StructTuple "move_binary_format::file_format::SignatureToken::MutableReference" [to_value x0]
      | TypeParameter  x0 => Value.StructTuple "move_binary_format::file_format::SignatureToken::TypeParameter" [to_value x0]
      | U16 => Value.StructTuple "move_binary_format::file_format::SignatureToken::U16" []
      | U32 => Value.StructTuple "move_binary_format::file_format::SignatureToken::U32" []
      | U256 => Value.StructTuple "move_binary_format::file_format::SignatureToken::U256" []
      end
  }.
End SignatureToken.

Module Signature.
  Inductive t : Set :=
  | Make : alloc.vec.Vec.t move_binary_format.file_format.SignatureToken.t alloc.alloc.Global.t -> t.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::Signature";
    to_value '(Make x0) :=
      Value.StructTuple "move_binary_format::file_format::Signature" [to_value x0];
  }.
End Signature.

Module CompiledModule.
  Record t : Set := {
    version: u32.t;
    self_module_handle_idx: move_binary_format.file_format.ModuleHandleIndex.t;
    module_handles: alloc.vec.Vec.t move_binary_format.file_format.ModuleHandle.t alloc.alloc.Global.t;
    struct_handles: alloc.vec.Vec.t move_binary_format.file_format.StructHandle.t alloc.alloc.Global.t;
    function_handles: alloc.vec.Vec.t move_binary_format.file_format.FunctionHandle.t alloc.alloc.Global.t;
    field_handles: alloc.vec.Vec.t move_binary_format.file_format.FieldHandle.t alloc.alloc.Global.t;
    friend_decls: alloc.vec.Vec.t move_binary_format.file_format.ModuleHandle.t alloc.alloc.Global.t;
    struct_def_instantiations: alloc.vec.Vec.t move_binary_format.file_format.StructDefInstantiation.t alloc.alloc.Global.t;
    function_instantiations: alloc.vec.Vec.t move_binary_format.file_format.FunctionInstantiation.t alloc.alloc.Global.t;
    field_instantiations: alloc.vec.Vec.t move_binary_format.file_format.FieldInstantiation.t alloc.alloc.Global.t;
    signatures: alloc.vec.Vec.t move_binary_format.file_format.Signature.t alloc.alloc.Global.t;
    identifiers: alloc.vec.Vec.t move_core_types.identifier.Identifier.t alloc.alloc.Global.t;
    address_identifiers: alloc.vec.Vec.t move_core_types.account_address.AccountAddress.t alloc.alloc.Global.t;
    constant_pool: alloc.vec.Vec.t move_binary_format.file_format.Constant.t alloc.alloc.Global.t;
    metadata: alloc.vec.Vec.t move_core_types.metadata.Metadata.t alloc.alloc.Global.t;
    struct_defs: alloc.vec.Vec.t move_binary_format.file_format.StructDefinition.t alloc.alloc.Global.t;
    function_defs: alloc.vec.Vec.t move_binary_format.file_format.FunctionDefinition.t alloc.alloc.Global.t;
  }.

  Definition current_to_value (x: t) : Value.t :=
    match x with
    | Build_t version self_module_handle_idx module_handles struct_handles function_handles field_handles friend_decls struct_def_instantiations function_instantiations field_instantiations signatures identifiers address_identifiers constant_pool metadata struct_defs function_defs =>
      Value.StructRecord "move_binary_format::file_format::CompiledModule" [
        ("version", to_value version);
        ("self_module_handle_idx", to_value self_module_handle_idx);
        ("module_handles", to_value module_handles);
        ("struct_handles", to_value struct_handles);
        ("function_handles", to_value function_handles);
        ("field_handles", to_value field_handles);
        ("friend_decls", to_value friend_decls);
        ("struct_def_instantiations", to_value struct_def_instantiations);
        ("function_instantiations", to_value function_instantiations);
        ("field_instantiations", to_value field_instantiations);
        ("signatures", to_value signatures);
        ("identifiers", to_value identifiers);
        ("address_identifiers", to_value address_identifiers);
        ("constant_pool", to_value constant_pool);
        ("metadata", to_value metadata);
        ("struct_defs", to_value struct_defs);
        ("function_defs", to_value function_defs)
      ]
    end.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "move_binary_format::file_format::CompiledModule";
    to_value := to_value
  }.
End CompiledModule.
