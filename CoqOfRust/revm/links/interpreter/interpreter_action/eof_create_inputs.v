Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.revm.links.dependencies.
Require Import CoqOfRust.revm.links.primitives.bytecode.eof.

(*
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum EOFCreateKind {
    Tx {
        initdata: Bytes,
    },
    Opcode {
        initcode: Eof,
        input: Bytes,
        created_address: Address,
    },
}
*)

Module EOFCreateKind.
  Inductive t : Type :=
    | Tx (initdata : Bytes.t)
    | Opcode (initcode : Eof.t) (input : Bytes.t) (created_address : Address.t).

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::eof_create_input::EOFCreateKind";
    φ k :=
      match k with
      | Tx initdata =>
          Value.StructRecord "revm_interpreter::interpreter::eof_create_input::EOFCreateKind::Tx" [
            ("initdata", φ initdata)
          ]
      | Opcode initcode input created_address =>
          Value.StructRecord "revm_interpreter::interpreter::eof_create_input::EOFCreateKind::Opcode" [
            ("initcode", φ initcode);
            ("input", φ input);
            ("created_address", φ created_address)
          ]
      end;
  }.
End EOFCreateKind.

(*
impl EOFCreateKind {
    /// Returns created address
    pub fn created_address(&self) -> Option<&Address> {
        match self {
            EOFCreateKind::Opcode {
                created_address, ..
            } => Some(created_address),
            EOFCreateKind::Tx { .. } => None,
        }
    }
}
*)




(*
  /// Inputs for EOF create call.
  #[derive(Debug, Default, Clone, PartialEq, Eq)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct EOFCreateInput {
      /// Caller of Eof Craate
      pub caller: Address,
      /// New contract address.
      pub created_address: Address,
      /// Values of ether transfered
      pub value: U256,
      /// Init eof code that is going to be executed.
      pub eof_init_code: Eof,
      /// Gas limit for the create call.
      pub gas_limit: u64,
  }
*)

Module EOFCreateInputs.
  Record t : Set := {
    caller : Address.t;
    created_address : Address.t;
    value : U256.t;
    eof_init_code : Eof.t;
    gas_limit : U64.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::eof_create_input::EOFCreateInputs";
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::eof_create_input::EOFCreateInputs" [
        ("caller", φ x.(caller));
        ("created_address", φ x.(created_address));
        ("value", φ x.(value));
        ("eof_init_code", φ x.(eof_init_code));
        ("gas_limit", φ x.(gas_limit))
      ];
  }.
End EOFCreateInputs.

Module Impl_EOFCreateInputs.
  Definition Self := EOFCreateInputs.t.
  
  (*
      pub fn new(caller: Address, value: U256, gas_limit: u64, kind: EOFCreateKind) -> Self {
        //let (eof_init_code, input) = Eof::decode_dangling(tx.data.clone())?;
        EOFCreateInputs {
            caller,
            value,
            gas_limit,
            kind,
        }
    }
  *)

  Parameter address_default : Address.t.
  Parameter eof_decode : Bytes.t -> Eof.t.

  Definition new (caller : Address.t) (value : U256.t)
                 (gas_limit : U64.t) (kind : EOFCreateKind.t) : Self :=
    {| EOFCreateInputs.caller := caller;
       EOFCreateInputs.created_address :=
         match kind with
         | EOFCreateKind.Opcode _ _ addr => addr
         | EOFCreateKind.Tx _ => address_default
         end;
       EOFCreateInputs.value := value;
       EOFCreateInputs.eof_init_code :=
         match kind with
         | EOFCreateKind.Opcode code _ _ => code
         | EOFCreateKind.Tx data => eof_decode data
         end;
       EOFCreateInputs.gas_limit := gas_limit |}.
      
  (*
  pub fn new_opcode(
        caller: Address,
        created_address: Address,
        value: U256,
        eof_init_code: Eof,
        gas_limit: u64,
        input: Bytes,
    ) -> EOFCreateInputs {
        EOFCreateInputs::new(
            caller,
            value,
            gas_limit,
            EOFCreateKind::Opcode {
                initcode: eof_init_code,
                input,
                created_address,
            },
        )
    }
  *)

  Definition new_opcode (caller : Address.t) (created_address : Address.t)
                        (value : U256.t) (eof_init_code : Eof.t)
                        (gas_limit : U64.t) (input : Bytes.t) : Self :=
    new caller value gas_limit (EOFCreateKind.Opcode eof_init_code input created_address).

End Impl_EOFCreateInputs.

