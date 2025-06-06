(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module gas.
  Module constants.
    Definition value_ZERO (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 0 |))).
    
    Global Instance Instance_IsConstant_value_ZERO :
      M.IsFunction.C "revm_interpreter::gas::constants::ZERO" value_ZERO.
    Admitted.
    Global Typeclasses Opaque value_ZERO.
    
    Definition value_BASE (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 2 |))).
    
    Global Instance Instance_IsConstant_value_BASE :
      M.IsFunction.C "revm_interpreter::gas::constants::BASE" value_BASE.
    Admitted.
    Global Typeclasses Opaque value_BASE.
    
    Definition value_VERYLOW (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 3 |))).
    
    Global Instance Instance_IsConstant_value_VERYLOW :
      M.IsFunction.C "revm_interpreter::gas::constants::VERYLOW" value_VERYLOW.
    Admitted.
    Global Typeclasses Opaque value_VERYLOW.
    
    Definition value_DATA_LOADN_GAS (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 3 |))).
    
    Global Instance Instance_IsConstant_value_DATA_LOADN_GAS :
      M.IsFunction.C "revm_interpreter::gas::constants::DATA_LOADN_GAS" value_DATA_LOADN_GAS.
    Admitted.
    Global Typeclasses Opaque value_DATA_LOADN_GAS.
    
    Definition value_CONDITION_JUMP_GAS (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 4 |))).
    
    Global Instance Instance_IsConstant_value_CONDITION_JUMP_GAS :
      M.IsFunction.C
        "revm_interpreter::gas::constants::CONDITION_JUMP_GAS"
        value_CONDITION_JUMP_GAS.
    Admitted.
    Global Typeclasses Opaque value_CONDITION_JUMP_GAS.
    
    Definition value_RETF_GAS (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 3 |))).
    
    Global Instance Instance_IsConstant_value_RETF_GAS :
      M.IsFunction.C "revm_interpreter::gas::constants::RETF_GAS" value_RETF_GAS.
    Admitted.
    Global Typeclasses Opaque value_RETF_GAS.
    
    Definition value_DATA_LOAD_GAS (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 4 |))).
    
    Global Instance Instance_IsConstant_value_DATA_LOAD_GAS :
      M.IsFunction.C "revm_interpreter::gas::constants::DATA_LOAD_GAS" value_DATA_LOAD_GAS.
    Admitted.
    Global Typeclasses Opaque value_DATA_LOAD_GAS.
    
    Definition value_LOW (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 5 |))).
    
    Global Instance Instance_IsConstant_value_LOW :
      M.IsFunction.C "revm_interpreter::gas::constants::LOW" value_LOW.
    Admitted.
    Global Typeclasses Opaque value_LOW.
    
    Definition value_MID (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 8 |))).
    
    Global Instance Instance_IsConstant_value_MID :
      M.IsFunction.C "revm_interpreter::gas::constants::MID" value_MID.
    Admitted.
    Global Typeclasses Opaque value_MID.
    
    Definition value_HIGH (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 10 |))).
    
    Global Instance Instance_IsConstant_value_HIGH :
      M.IsFunction.C "revm_interpreter::gas::constants::HIGH" value_HIGH.
    Admitted.
    Global Typeclasses Opaque value_HIGH.
    
    Definition value_JUMPDEST (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 1 |))).
    
    Global Instance Instance_IsConstant_value_JUMPDEST :
      M.IsFunction.C "revm_interpreter::gas::constants::JUMPDEST" value_JUMPDEST.
    Admitted.
    Global Typeclasses Opaque value_JUMPDEST.
    
    Definition value_SELFDESTRUCT (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "i64", Value.Integer IntegerKind.I64 24000 |))).
    
    Global Instance Instance_IsConstant_value_SELFDESTRUCT :
      M.IsFunction.C "revm_interpreter::gas::constants::SELFDESTRUCT" value_SELFDESTRUCT.
    Admitted.
    Global Typeclasses Opaque value_SELFDESTRUCT.
    
    Definition value_CREATE (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 32000 |))).
    
    Global Instance Instance_IsConstant_value_CREATE :
      M.IsFunction.C "revm_interpreter::gas::constants::CREATE" value_CREATE.
    Admitted.
    Global Typeclasses Opaque value_CREATE.
    
    Definition value_CALLVALUE (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 9000 |))).
    
    Global Instance Instance_IsConstant_value_CALLVALUE :
      M.IsFunction.C "revm_interpreter::gas::constants::CALLVALUE" value_CALLVALUE.
    Admitted.
    Global Typeclasses Opaque value_CALLVALUE.
    
    Definition value_NEWACCOUNT (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 25000 |))).
    
    Global Instance Instance_IsConstant_value_NEWACCOUNT :
      M.IsFunction.C "revm_interpreter::gas::constants::NEWACCOUNT" value_NEWACCOUNT.
    Admitted.
    Global Typeclasses Opaque value_NEWACCOUNT.
    
    Definition value_EXP (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 10 |))).
    
    Global Instance Instance_IsConstant_value_EXP :
      M.IsFunction.C "revm_interpreter::gas::constants::EXP" value_EXP.
    Admitted.
    Global Typeclasses Opaque value_EXP.
    
    Definition value_MEMORY (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 3 |))).
    
    Global Instance Instance_IsConstant_value_MEMORY :
      M.IsFunction.C "revm_interpreter::gas::constants::MEMORY" value_MEMORY.
    Admitted.
    Global Typeclasses Opaque value_MEMORY.
    
    Definition value_LOG (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 375 |))).
    
    Global Instance Instance_IsConstant_value_LOG :
      M.IsFunction.C "revm_interpreter::gas::constants::LOG" value_LOG.
    Admitted.
    Global Typeclasses Opaque value_LOG.
    
    Definition value_LOGDATA (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 8 |))).
    
    Global Instance Instance_IsConstant_value_LOGDATA :
      M.IsFunction.C "revm_interpreter::gas::constants::LOGDATA" value_LOGDATA.
    Admitted.
    Global Typeclasses Opaque value_LOGDATA.
    
    Definition value_LOGTOPIC (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 375 |))).
    
    Global Instance Instance_IsConstant_value_LOGTOPIC :
      M.IsFunction.C "revm_interpreter::gas::constants::LOGTOPIC" value_LOGTOPIC.
    Admitted.
    Global Typeclasses Opaque value_LOGTOPIC.
    
    Definition value_KECCAK256 (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 30 |))).
    
    Global Instance Instance_IsConstant_value_KECCAK256 :
      M.IsFunction.C "revm_interpreter::gas::constants::KECCAK256" value_KECCAK256.
    Admitted.
    Global Typeclasses Opaque value_KECCAK256.
    
    Definition value_KECCAK256WORD (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 6 |))).
    
    Global Instance Instance_IsConstant_value_KECCAK256WORD :
      M.IsFunction.C "revm_interpreter::gas::constants::KECCAK256WORD" value_KECCAK256WORD.
    Admitted.
    Global Typeclasses Opaque value_KECCAK256WORD.
    
    Definition value_COPY (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 3 |))).
    
    Global Instance Instance_IsConstant_value_COPY :
      M.IsFunction.C "revm_interpreter::gas::constants::COPY" value_COPY.
    Admitted.
    Global Typeclasses Opaque value_COPY.
    
    Definition value_BLOCKHASH (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 20 |))).
    
    Global Instance Instance_IsConstant_value_BLOCKHASH :
      M.IsFunction.C "revm_interpreter::gas::constants::BLOCKHASH" value_BLOCKHASH.
    Admitted.
    Global Typeclasses Opaque value_BLOCKHASH.
    
    Definition value_CODEDEPOSIT (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 200 |))).
    
    Global Instance Instance_IsConstant_value_CODEDEPOSIT :
      M.IsFunction.C "revm_interpreter::gas::constants::CODEDEPOSIT" value_CODEDEPOSIT.
    Admitted.
    Global Typeclasses Opaque value_CODEDEPOSIT.
    
    Definition value_ISTANBUL_SLOAD_GAS (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 800 |))).
    
    Global Instance Instance_IsConstant_value_ISTANBUL_SLOAD_GAS :
      M.IsFunction.C
        "revm_interpreter::gas::constants::ISTANBUL_SLOAD_GAS"
        value_ISTANBUL_SLOAD_GAS.
    Admitted.
    Global Typeclasses Opaque value_ISTANBUL_SLOAD_GAS.
    
    Definition value_SSTORE_SET (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 20000 |))).
    
    Global Instance Instance_IsConstant_value_SSTORE_SET :
      M.IsFunction.C "revm_interpreter::gas::constants::SSTORE_SET" value_SSTORE_SET.
    Admitted.
    Global Typeclasses Opaque value_SSTORE_SET.
    
    Definition value_SSTORE_RESET (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 5000 |))).
    
    Global Instance Instance_IsConstant_value_SSTORE_RESET :
      M.IsFunction.C "revm_interpreter::gas::constants::SSTORE_RESET" value_SSTORE_RESET.
    Admitted.
    Global Typeclasses Opaque value_SSTORE_RESET.
    
    Definition value_REFUND_SSTORE_CLEARS
        (ε : list Value.t)
        (τ : list Ty.t)
        (α : list Value.t)
        : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "i64", Value.Integer IntegerKind.I64 15000 |))).
    
    Global Instance Instance_IsConstant_value_REFUND_SSTORE_CLEARS :
      M.IsFunction.C
        "revm_interpreter::gas::constants::REFUND_SSTORE_CLEARS"
        value_REFUND_SSTORE_CLEARS.
    Admitted.
    Global Typeclasses Opaque value_REFUND_SSTORE_CLEARS.
    
    Definition value_TRANSACTION_ZERO_DATA
        (ε : list Value.t)
        (τ : list Ty.t)
        (α : list Value.t)
        : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 4 |))).
    
    Global Instance Instance_IsConstant_value_TRANSACTION_ZERO_DATA :
      M.IsFunction.C
        "revm_interpreter::gas::constants::TRANSACTION_ZERO_DATA"
        value_TRANSACTION_ZERO_DATA.
    Admitted.
    Global Typeclasses Opaque value_TRANSACTION_ZERO_DATA.
    
    Definition value_TRANSACTION_NON_ZERO_DATA_INIT
        (ε : list Value.t)
        (τ : list Ty.t)
        (α : list Value.t)
        : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 16 |))).
    
    Global Instance Instance_IsConstant_value_TRANSACTION_NON_ZERO_DATA_INIT :
      M.IsFunction.C
        "revm_interpreter::gas::constants::TRANSACTION_NON_ZERO_DATA_INIT"
        value_TRANSACTION_NON_ZERO_DATA_INIT.
    Admitted.
    Global Typeclasses Opaque value_TRANSACTION_NON_ZERO_DATA_INIT.
    
    Definition value_TRANSACTION_NON_ZERO_DATA_FRONTIER
        (ε : list Value.t)
        (τ : list Ty.t)
        (α : list Value.t)
        : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 68 |))).
    
    Global Instance Instance_IsConstant_value_TRANSACTION_NON_ZERO_DATA_FRONTIER :
      M.IsFunction.C
        "revm_interpreter::gas::constants::TRANSACTION_NON_ZERO_DATA_FRONTIER"
        value_TRANSACTION_NON_ZERO_DATA_FRONTIER.
    Admitted.
    Global Typeclasses Opaque value_TRANSACTION_NON_ZERO_DATA_FRONTIER.
    
    Definition value_EOF_CREATE_GAS (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 32000 |))).
    
    Global Instance Instance_IsConstant_value_EOF_CREATE_GAS :
      M.IsFunction.C "revm_interpreter::gas::constants::EOF_CREATE_GAS" value_EOF_CREATE_GAS.
    Admitted.
    Global Typeclasses Opaque value_EOF_CREATE_GAS.
    
    Definition value_ACCESS_LIST_ADDRESS
        (ε : list Value.t)
        (τ : list Ty.t)
        (α : list Value.t)
        : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 2400 |))).
    
    Global Instance Instance_IsConstant_value_ACCESS_LIST_ADDRESS :
      M.IsFunction.C
        "revm_interpreter::gas::constants::ACCESS_LIST_ADDRESS"
        value_ACCESS_LIST_ADDRESS.
    Admitted.
    Global Typeclasses Opaque value_ACCESS_LIST_ADDRESS.
    
    Definition value_ACCESS_LIST_STORAGE_KEY
        (ε : list Value.t)
        (τ : list Ty.t)
        (α : list Value.t)
        : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 1900 |))).
    
    Global Instance Instance_IsConstant_value_ACCESS_LIST_STORAGE_KEY :
      M.IsFunction.C
        "revm_interpreter::gas::constants::ACCESS_LIST_STORAGE_KEY"
        value_ACCESS_LIST_STORAGE_KEY.
    Admitted.
    Global Typeclasses Opaque value_ACCESS_LIST_STORAGE_KEY.
    
    Definition value_COLD_SLOAD_COST (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 2100 |))).
    
    Global Instance Instance_IsConstant_value_COLD_SLOAD_COST :
      M.IsFunction.C "revm_interpreter::gas::constants::COLD_SLOAD_COST" value_COLD_SLOAD_COST.
    Admitted.
    Global Typeclasses Opaque value_COLD_SLOAD_COST.
    
    Definition value_COLD_ACCOUNT_ACCESS_COST
        (ε : list Value.t)
        (τ : list Ty.t)
        (α : list Value.t)
        : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 2600 |))).
    
    Global Instance Instance_IsConstant_value_COLD_ACCOUNT_ACCESS_COST :
      M.IsFunction.C
        "revm_interpreter::gas::constants::COLD_ACCOUNT_ACCESS_COST"
        value_COLD_ACCOUNT_ACCESS_COST.
    Admitted.
    Global Typeclasses Opaque value_COLD_ACCOUNT_ACCESS_COST.
    
    Definition value_WARM_STORAGE_READ_COST
        (ε : list Value.t)
        (τ : list Ty.t)
        (α : list Value.t)
        : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 100 |))).
    
    Global Instance Instance_IsConstant_value_WARM_STORAGE_READ_COST :
      M.IsFunction.C
        "revm_interpreter::gas::constants::WARM_STORAGE_READ_COST"
        value_WARM_STORAGE_READ_COST.
    Admitted.
    Global Typeclasses Opaque value_WARM_STORAGE_READ_COST.
    
    Definition value_WARM_SSTORE_RESET (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic
        (M.alloc (|
          Ty.path "u64",
          M.call_closure (|
            Ty.path "u64",
            BinOp.Wrap.sub,
            [
              M.read (|
                get_constant (| "revm_interpreter::gas::constants::SSTORE_RESET", Ty.path "u64" |)
              |);
              M.read (|
                get_constant (|
                  "revm_interpreter::gas::constants::COLD_SLOAD_COST",
                  Ty.path "u64"
                |)
              |)
            ]
          |)
        |))).
    
    Global Instance Instance_IsConstant_value_WARM_SSTORE_RESET :
      M.IsFunction.C "revm_interpreter::gas::constants::WARM_SSTORE_RESET" value_WARM_SSTORE_RESET.
    Admitted.
    Global Typeclasses Opaque value_WARM_SSTORE_RESET.
    
    Definition value_INITCODE_WORD_COST (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 2 |))).
    
    Global Instance Instance_IsConstant_value_INITCODE_WORD_COST :
      M.IsFunction.C
        "revm_interpreter::gas::constants::INITCODE_WORD_COST"
        value_INITCODE_WORD_COST.
    Admitted.
    Global Typeclasses Opaque value_INITCODE_WORD_COST.
    
    Definition value_CALL_STIPEND (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic (M.alloc (| Ty.path "u64", Value.Integer IntegerKind.U64 2300 |))).
    
    Global Instance Instance_IsConstant_value_CALL_STIPEND :
      M.IsFunction.C "revm_interpreter::gas::constants::CALL_STIPEND" value_CALL_STIPEND.
    Admitted.
    Global Typeclasses Opaque value_CALL_STIPEND.
    
    Definition value_MIN_CALLEE_GAS (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      ltac:(M.monadic
        (get_constant (| "revm_interpreter::gas::constants::CALL_STIPEND", Ty.path "u64" |))).
    
    Global Instance Instance_IsConstant_value_MIN_CALLEE_GAS :
      M.IsFunction.C "revm_interpreter::gas::constants::MIN_CALLEE_GAS" value_MIN_CALLEE_GAS.
    Admitted.
    Global Typeclasses Opaque value_MIN_CALLEE_GAS.
  End constants.
End gas.
