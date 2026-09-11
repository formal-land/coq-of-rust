From Stdlib Require Import List ZArith.

Require Import RocqOfRust.RocqOfRust.
Require Import alloc.links.raw_vec.
Require Import alloc.vec.links.mod.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed_FixedBytes.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.bytes.simulate.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.links.common.
Require Import alloy_primitives.log.links.mod.
Require Import bytes.links.bytes.
Require Import core.links.result.
Require Import links.M.
Require Import revm.revm_context_interface.links.cfg.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.links.transaction.
Require Import revm.revm_context_interface.simulate.block.
Require Import revm.revm_context_interface.simulate.cfg.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_context_interface.simulate.transaction.
Require Import ruint.links.lib.
Require Import ruint.simulate.lib.
Require Import simulate.M.

Import ListNotations.

Open Scope Z_scope.
Open Scope pstring_scope.

(** Stateful host used to execute interpreter programs against an explicit
    environment and account model. *)
Module StatefulHost.
  Module Environment.
    Module Block.
      Record t : Set := {
        coinbase : Z;
        gas_limit : Z;
        number : Z;
        timestamp : Z;
        difficulty : Z;
        base_fee : Z;
        blob_base_fee : Z;
        previous_randao : option Z;
        hashes : list (Z * Z);
      }.
    End Block.

    Module Transaction.
      Record t : Set := {
        chain_id : Z;
        gas_price : Z;
        blob_hashes : list Z;
      }.
    End Transaction.

    Module Call.
      Record t : Set := {
        caller : Z;
      }.
    End Call.
  End Environment.

  Module Account.
    Record t : Set := {
      address : Z;
      balance : Z;
      nonce : Z;
      code : list Z;
      code_hash : Z;
      storage : list (Z * Z);
      transient_storage : list (Z * Z);
    }.
  End Account.

  Module EvmLog.
    Record t : Set := {
      address : Z;
      topics : list Z;
      data : list Z;
    }.
  End EvmLog.

  Module Change.
    Inductive t : Set :=
    | Balance (address value : Z)
    | Nonce (address nonce : Z)
    | Code (address : Z) (code : list Z)
    | Storage (address key value : Z)
    | TransientStorage (address key value : Z)
    | Created (address : Z)
    | SelfDestruct (address : Z).
  End Change.

  Module Input.
    Record t : Set := {
      block : Environment.Block.t;
      transaction : Environment.Transaction.t;
      call : Environment.Call.t;
      state : list Account.t;
    }.
  End Input.
Module RustBlock := revm.revm_context_interface.simulate.block.Block.
Module RustCfg := revm.revm_context_interface.simulate.cfg.Cfg.
Module RustCfgTypes := revm.revm_context_interface.links.cfg.Cfg.Types.
Module RustCfgGetterTypes :=
  revm.revm_context_interface.links.cfg.CfgGetter.Types.
Module RustTransaction :=
  revm.revm_context_interface.simulate.transaction.Transaction.
Module RustTransactionTypes :=
  revm.revm_context_interface.links.transaction.Transaction.Types.

  Record t : Set := {
    input : Input.t;
    accounts : list Account.t;
    accessed_accounts : list Z;
    accessed_storage : list (Z * Z);
    logs : list EvmLog.t;
    state_changes : list Change.t;
  }.

  Definition make (input : Input.t) : t :=
    {| input := input;
       accounts := input.(Input.state);
       accessed_accounts := [];
       accessed_storage := [];
       logs := [];
       state_changes := [] |}.

  Definition observe_logs (host : t) : list EvmLog.t :=
    host.(logs).

  Definition observe_state_changes (host : t) : list Change.t :=
    host.(state_changes).

  Global Instance IsLink : Link t :=
    {| Φ := Ty.path "revm::revm_interpreter::tests::StatefulHost";
       φ _ := Value.Tuple [] |}.

  Definition identity_ref : RefStub.t t t :=
    {| RefStub.path := [];
       RefStub.projection self := self;
       RefStub.injection _ value := value |}.

  Definition transaction_types : RustTransactionTypes.t :=
    {| RustTransactionTypes.TransactionError := t;
       RustTransactionTypes.TransactionType := t;
       RustTransactionTypes.AccessList := t;
       RustTransactionTypes.Legacy := t;
       RustTransactionTypes.Eip2930 := t;
       RustTransactionTypes.Eip1559 := t;
       RustTransactionTypes.Eip4844 := t;
       RustTransactionTypes.Eip7702 := t |}.

  Global Instance TransactionTypesAreLinks :
      RustTransactionTypes.AreLinks transaction_types := {}.

  Definition host_types : Host.Types.t :=
    {| Host.Types.Transaction := t;
       Host.Types.TransactionTypes := transaction_types;
       Host.Types.Cfg := t;
       Host.Types.Spec := t;
       Host.Types.Block := t |}.

  Global Instance HostTypesAreLinks : Host.Types.AreLinks host_types := {}.

  Global Instance CfgTypesAreLinks :
      RustCfgTypes.AreLinks
        (RustCfgGetterTypes.to_Cfg_types
          (Host.Types.to_CfgGetter_types host_types)) := {}.

  Global Instance TransactionForHost :
      @RustTransaction.C
        t IsLink transaction_types TransactionTypesAreLinks.
  Proof.
    unshelve econstructor.
    - exact (fun self => self).
    - exact identity_ref.
    - exact identity_ref.
    - exact identity_ref.
    - exact identity_ref.
    - exact identity_ref.
    - exact (fun self =>
        {| M.Integer.value :=
             self.(input).(Input.transaction).(Environment.Transaction.gas_price) |}).
    - exact (fun self _ =>
        {| M.Integer.value :=
             self.(input).(Input.transaction).(Environment.Transaction.gas_price) |}).
    - exact (fun _ => TxKind.Create).
    - exact (fun _ => None).
  Defined.

  Global Instance TransactionGetterForHost :
      TransactionGetter.C t t transaction_types :=
    {| TransactionGetter.Transaction_for_Transaction := TransactionForHost;
       TransactionGetter.tx := (identity_ref : RefStub.t t t) |}.

  Global Instance BlockForHost : RustBlock.C t :=
    {| RustBlock.number self :=
         {| M.Integer.value :=
              self.(input).(Input.block).(Environment.Block.number) |};
       RustBlock.beneficiary self :=
         {| Address.value :=
              self.(input).(Input.block).(Environment.Block.coinbase) |};
       RustBlock.timestamp self :=
         {| M.Integer.value :=
              self.(input).(Input.block).(Environment.Block.timestamp) |};
       RustBlock.gas_limit self :=
         {| M.Integer.value :=
              self.(input).(Input.block).(Environment.Block.gas_limit) |};
       RustBlock.basefee self :=
         {| M.Integer.value :=
              self.(input).(Input.block).(Environment.Block.base_fee) |};
       RustBlock.difficulty self :=
         {| Uint.value :=
              self.(input).(Input.block).(Environment.Block.difficulty) |};
       RustBlock.prevrandao self :=
         match self.(input).(Input.block).(Environment.Block.previous_randao) with
         | Some value =>
             Some
               (Impl_From_U256_for_FixedBytes_32.from
                 {| Uint.value := value |})
         | None => None
         end;
       RustBlock.blob_excess_gas_and_price _ := None;
       RustBlock.blob_gasprice self :=
         Some
           {| M.Integer.value :=
                self.(input).(Input.block).(Environment.Block.blob_base_fee) |};
       RustBlock.blob_excess_gas _ := None |}.

  Global Instance BlockGetterForHost :
      BlockGetter.C t (Host.Types.to_BlockGetter_types host_types) :=
    {| BlockGetter.Block_for_Block := BlockForHost;
       BlockGetter.block := (identity_ref : RefStub.t t t) |}.

  Global Instance CfgForHost :
      @RustCfg.C
        t IsLink
        (RustCfgGetterTypes.to_Cfg_types
          (Host.Types.to_CfgGetter_types host_types))
        CfgTypesAreLinks.
  Proof.
    constructor.
    - exact (fun self =>
        {| M.Integer.value :=
             self.(input).(Input.transaction).(Environment.Transaction.chain_id) |}).
    - exact (fun self => self).
    - exact (fun _ => {| M.Integer.value := 24576 |}).
    - exact (fun _ => false).
    - exact (fun _ => false).
    - exact (fun _ => false).
    - exact (fun _ => false).
    - exact (fun _ => false).
    - exact (fun _ => false).
  Defined.

  Global Instance CfgGetterForHost :
      CfgGetter.C t (Host.Types.to_CfgGetter_types host_types) :=
    {| CfgGetter.Cfg_for_Cfg := CfgForHost;
       CfgGetter.cfg := (identity_ref : RefStub.t t t) |}.

  Definition append_change (host : t) (change : Change.t) : t :=
    {| input := host.(input);
       accounts := host.(accounts);
       accessed_accounts := host.(accessed_accounts);
       accessed_storage := host.(accessed_storage);
       logs := host.(logs);
       state_changes := host.(state_changes) ++ [change] |}.

  Definition append_log (host : t) (entry : Log.t LogData.t) : t :=
    let data := entry.(Log.data) in
    {| input := host.(input);
       accounts := host.(accounts);
       accessed_accounts := host.(accessed_accounts);
       accessed_storage := host.(accessed_storage);
       logs := host.(logs) ++
         [{| EvmLog.address := entry.(Log.address).(Address.value);
             EvmLog.topics :=
               List.map Uint.value data.(LogData.topics).(Vec.buf).(RawVec.value);
             EvmLog.data :=
               List.map M.Integer.value
                 data.(LogData.data)
                   .(alloy_primitives.bytes.links.mod.Bytes.value)
                   .(bytes.Bytes.value) |}];
       state_changes := host.(state_changes) |}.

  Definition rust_address (value : Z) : Address.t :=
    {| Address.value := value |}.

  Definition rust_word (value : Z) : aliases.U256.t :=
    {| Uint.value := value |}.

  Definition rust_byte (value : Z) : u8 :=
    {| M.Integer.value := value |}.

  Fixpoint find_account
      (address : Z) (accounts : list Account.t) :
      option Account.t :=
    match accounts with
    | [] => None
    | account :: accounts =>
        if account.(Account.address) =? address
        then Some account
        else find_account address accounts
    end.

  Fixpoint lookup_word (key : Z) (entries : list (Z * Z)) : Z :=
    match entries with
    | [] => 0
    | (entry_key, value) :: entries =>
        if entry_key =? key then value else lookup_word key entries
    end.

  Fixpoint lookup_z (key : Z) (entries : list (Z * Z)) : option Z :=
    match entries with
    | [] => None
    | (entry_key, value) :: entries =>
        if entry_key =? key then Some value else lookup_z key entries
    end.

  Fixpoint update_word
      (key value : Z) (entries : list (Z * Z)) : list (Z * Z) :=
    match entries with
    | [] => [(key, value)]
    | (entry_key, entry_value) :: entries =>
        if entry_key =? key
        then (key, value) :: entries
        else (entry_key, entry_value) :: update_word key value entries
    end.

  Definition empty_account (address : Z) : Account.t :=
    {| Account.address := address;
       Account.balance := 0;
       Account.nonce := 0;
       Account.code := [];
       Account.code_hash := 0;
       Account.storage := [];
       Account.transient_storage := [] |}.

  Definition account_with_storage
      (account : Account.t) (key value : Z) : Account.t :=
    {| Account.address := account.(Account.address);
       Account.balance := account.(Account.balance);
       Account.nonce := account.(Account.nonce);
       Account.code := account.(Account.code);
       Account.code_hash := account.(Account.code_hash);
       Account.storage := update_word key value account.(Account.storage);
       Account.transient_storage := account.(Account.transient_storage) |}.

  Definition account_with_transient_storage
      (account : Account.t) (key value : Z) : Account.t :=
    {| Account.address := account.(Account.address);
       Account.balance := account.(Account.balance);
       Account.nonce := account.(Account.nonce);
       Account.code := account.(Account.code);
       Account.code_hash := account.(Account.code_hash);
       Account.storage := account.(Account.storage);
       Account.transient_storage :=
         update_word key value account.(Account.transient_storage) |}.

  Definition account_with_balance
      (account : Account.t) (balance : Z) : Account.t :=
    {| Account.address := account.(Account.address);
       Account.balance := balance;
       Account.nonce := account.(Account.nonce);
       Account.code := account.(Account.code);
       Account.code_hash := account.(Account.code_hash);
       Account.storage := account.(Account.storage);
       Account.transient_storage := account.(Account.transient_storage) |}.

  Fixpoint update_account
      (address : Z)
      (update : Account.t -> Account.t)
      (accounts : list Account.t) : list Account.t :=
    match accounts with
    | [] => [update (empty_account address)]
    | account :: accounts =>
        if account.(Account.address) =? address
        then update account :: accounts
        else account :: update_account address update accounts
    end.

  Definition with_accounts (host : t) (accounts : list Account.t) : t :=
    {| input := host.(input);
       accounts := accounts;
       accessed_accounts := host.(accessed_accounts);
       accessed_storage := host.(accessed_storage);
       logs := host.(logs);
       state_changes := host.(state_changes) |}.

  Fixpoint storage_is_warm
      (address key : Z) (accessed_storage : list (Z * Z)) : bool :=
    match accessed_storage with
    | [] => false
    | (accessed_address, accessed_key) :: accessed_storage =>
        ((accessed_address =? address) && (accessed_key =? key)) ||
        storage_is_warm address key accessed_storage
    end.

  Definition storage_is_cold (host : t) (address key : Z) : bool :=
    negb (storage_is_warm address key host.(accessed_storage)).

  Definition mark_storage_warm (host : t) (address key : Z) : t :=
    if storage_is_warm address key host.(accessed_storage) then
      host
    else
      {| input := host.(input);
         accounts := host.(accounts);
         accessed_accounts := host.(accessed_accounts);
         accessed_storage := (address, key) :: host.(accessed_storage);
         logs := host.(logs);
         state_changes := host.(state_changes) |}.

  Definition balance (host : t) (address : Address.t) :
      option (StateLoad.t aliases.U256.t) * t :=
    let value :=
      match find_account address.(Address.value) host.(accounts) with
      | Some account => account.(Account.balance)
      | None => 0
      end in
    (Some {| StateLoad.data := rust_word value;
             StateLoad.is_cold := false |}, host).

  Definition account_is_empty (account : Account.t) : bool :=
    (account.(Account.balance) =? 0) &&
    (account.(Account.nonce) =? 0) &&
    match account.(Account.code) with
    | [] => true
    | _ => false
    end.

  Definition account_is_warm (host : t) (address : Z) : bool :=
    List.existsb (Z.eqb address) host.(accessed_accounts).

  Definition warm_account (host : t) (address : Z) : t :=
    if account_is_warm host address then host
    else
      {| input := host.(input);
         accounts := host.(accounts);
         accessed_accounts := address :: host.(accessed_accounts);
         accessed_storage := host.(accessed_storage);
         logs := host.(logs);
         state_changes := host.(state_changes) |}.

  Definition warm_access_list (host : t) (entries : list (Z * list Z)) : t :=
    List.fold_left
      (fun host entry =>
        let '(address, keys) := entry in
        List.fold_left
          (fun host key => mark_storage_warm host address key)
          keys (warm_account host address))
      entries host.

  Definition account_info_load
      (host : t) (address : Address.t) : AccountInfoLoad.t :=
    let account :=
      match find_account address.(Address.value) host.(accounts) with
      | Some account => account
      | None => empty_account address.(Address.value)
      end in
    {| AccountInfoLoad.account :=
         Cow.Owned
           {| AccountInfo.balance := rust_word account.(Account.balance);
              AccountInfo.nonce :=
                {| M.Integer.value := account.(Account.nonce) |};
              AccountInfo.code_hash :=
                Impl_From_U256_for_FixedBytes_32.from
                  (rust_word account.(Account.code_hash));
              AccountInfo.code := None |};
       AccountInfoLoad.is_cold := negb (account_is_warm host address.(Address.value));
       AccountInfoLoad.is_empty := account_is_empty account |}.

  Definition load_account_info_skip_cold_load
      (host : t) (address : Address.t) (skip_cold_load : bool) :
      Result.t AccountInfoLoad.t LoadError.t * t :=
    if skip_cold_load && negb (account_is_warm host address.(Address.value)) then
      (Result.Err LoadError.ColdLoadSkipped, host)
    else
      (Result.Ok (account_info_load host address),
       warm_account host address.(Address.value)).

  Definition load_account_delegated
      (host : t) (address : Address.t) :
      option (StateLoad.t AccountLoad.t) * t :=
    let account :=
      match find_account address.(Address.value) host.(accounts) with
      | Some account => account
      | None => empty_account address.(Address.value)
      end in
    (Some
      {| StateLoad.data :=
           {| AccountLoad.is_delegate_account_cold := None;
              AccountLoad.is_empty := account_is_empty account |};
         StateLoad.is_cold := false |}, host).

  Definition code (host : t) (address : Address.t) :
      option
        (Eip7702CodeLoad.t alloy_primitives.bytes.links.mod.Bytes.t) * t :=
    let value :=
      match find_account address.(Address.value) host.(accounts) with
      | Some account => account.(Account.code)
      | None => []
      end in
    (Some
      {| Eip7702CodeLoad.state_load :=
           {| StateLoad.data :=
                Impl_Bytes.copy_from_slice (List.map rust_byte value);
              StateLoad.is_cold := false |};
         Eip7702CodeLoad.is_delegate_account_cold := None |}, host).

  Definition load_account_code (host : t) (address : Address.t) :
      option (StateLoad.t alloy_primitives.bytes.links.mod.Bytes.t) * t :=
    let value :=
      match find_account address.(Address.value) host.(accounts) with
      | Some account => account.(Account.code)
      | None => []
      end in
    (Some
      {| StateLoad.data :=
           Impl_Bytes.copy_from_slice (List.map rust_byte value);
         StateLoad.is_cold := false |}, host).

  Definition sload
      (host : t) (address : Address.t) (key : aliases.U256.t) :
      option (StateLoad.t aliases.U256.t) * t :=
    let address_value := address.(Address.value) in
    let key_value := key.(Uint.value) in
    let is_cold := storage_is_cold host address_value key_value in
    let value :=
      match find_account address_value host.(accounts) with
      | Some account => lookup_word key_value account.(Account.storage)
      | None => 0
      end in
    let host := mark_storage_warm host address_value key_value in
    (Some {| StateLoad.data := rust_word value;
             StateLoad.is_cold := is_cold |}, host).

  Definition code_hash (host : t) (address : Address.t) :
      option (Eip7702CodeLoad.t aliases.B256.t) * t :=
    let value :=
      match find_account address.(Address.value) host.(accounts) with
      | Some account => account.(Account.code_hash)
      | None => 0
      end in
    (Some
      {| Eip7702CodeLoad.state_load :=
           {| StateLoad.data :=
                Impl_From_U256_for_FixedBytes_32.from (rust_word value);
              StateLoad.is_cold := false |};
         Eip7702CodeLoad.is_delegate_account_cold := None |}, host).

  Definition sstore
      (host : t) (address : Address.t)
      (key value : aliases.U256.t) :
      option (StateLoad.t SStoreResult.t) * t :=
    let address_value := address.(Address.value) in
    let key_value := key.(Uint.value) in
    let new_value := value.(Uint.value) in
    let is_cold := storage_is_cold host address_value key_value in
    let present_value :=
      match find_account address_value host.(accounts) with
      | Some account => lookup_word key_value account.(Account.storage)
      | None => 0
      end in
    let original_value :=
      match find_account address_value host.(input).(Input.state) with
      | Some account => lookup_word key_value account.(Account.storage)
      | None => 0
      end in
    let accounts :=
      update_account address_value
        (fun account => account_with_storage account key_value new_value)
        host.(accounts) in
    let host := with_accounts host accounts in
    let host := mark_storage_warm host address_value key_value in
    let host := append_change host
      (Change.Storage address_value key_value new_value) in
    (Some
      {| StateLoad.data :=
           {| SStoreResult.original_value := rust_word original_value;
              SStoreResult.present_value := rust_word present_value;
              SStoreResult.new_value := value |};
         StateLoad.is_cold := is_cold |}, host).

  Definition tload
      (host : t) (address : Address.t) (key : aliases.U256.t) :
      aliases.U256.t * t :=
    let value :=
      match find_account address.(Address.value) host.(accounts) with
      | Some account =>
          lookup_word key.(Uint.value) account.(Account.transient_storage)
      | None => 0
      end in
    (rust_word value, host).

  Definition tstore
      (host : t) (address : Address.t)
      (key value : aliases.U256.t) : t :=
    let address_value := address.(Address.value) in
    let key_value := key.(Uint.value) in
    let new_value := value.(Uint.value) in
    let accounts :=
      update_account address_value
        (fun account =>
          account_with_transient_storage account key_value new_value)
        host.(accounts) in
    append_change (with_accounts host accounts)
      (Change.TransientStorage address_value key_value new_value).

  Definition sload_skip_cold_load
      (host : t) (address : Address.t) (key : aliases.U256.t)
      (skip_cold : bool) :
      Result.t (StateLoad.t aliases.U256.t) LoadError.t * t :=
    if skip_cold &&
       storage_is_cold host address.(Address.value) key.(Uint.value) then
      (Result.Err LoadError.ColdLoadSkipped, host)
    else
      let '(result, host) := sload host address key in
      (match result with
       | Some value => Result.Ok value
       | None => Result.Err LoadError.DBError
       end, host).

  Definition sstore_skip_cold_load
      (host : t) (address : Address.t)
      (key value : aliases.U256.t) (skip_cold : bool) :
      Result.t (StateLoad.t SStoreResult.t) LoadError.t * t :=
    if skip_cold &&
       storage_is_cold host address.(Address.value) key.(Uint.value) then
      (Result.Err LoadError.ColdLoadSkipped, host)
    else
      let '(result, host) := sstore host address key value in
      (match result with
       | Some value => Result.Ok value
       | None => Result.Err LoadError.DBError
       end, host).

  Fixpoint was_selfdestructed
      (address : Z) (changes : list Change.t) : bool :=
    match changes with
    | [] => false
    | Change.SelfDestruct changed_address :: changes =>
        (changed_address =? address) || was_selfdestructed address changes
    | _ :: changes => was_selfdestructed address changes
    end.

  Definition selfdestruct
      (host : t) (address target : Address.t) :
      Result.t (StateLoad.t SelfDestructResult.t) LoadError.t * t :=
    let address_value := address.(Address.value) in
    let target_value := target.(Address.value) in
    let source :=
      match find_account address_value host.(accounts) with
      | Some account => account
      | None => empty_account address_value
      end in
    let target_exists :=
      match find_account target_value host.(accounts) with
      | Some _ => true
      | None => false
      end in
    let target_balance :=
      match find_account target_value host.(accounts) with
      | Some account => account.(Account.balance)
      | None => 0
      end in
    let previously_destroyed :=
      was_selfdestructed address_value host.(state_changes) in
    let transferred_balance :=
      (target_balance + source.(Account.balance)) mod 2 ^ 256 in
    let accounts :=
      update_account address_value
        (fun account => account_with_balance account 0)
        host.(accounts) in
    let accounts :=
      if address_value =? target_value
      then accounts
      else
        update_account target_value
          (fun account =>
            account_with_balance account transferred_balance)
          accounts in
    let host := with_accounts host accounts in
    let host := append_change host
      (Change.Balance address_value 0) in
    let host :=
      if address_value =? target_value
      then host
      else append_change host
        (Change.Balance target_value
          transferred_balance) in
    let host := append_change host (Change.SelfDestruct address_value) in
    (Result.Ok
      {| StateLoad.data :=
           {| SelfDestructResult.had_value :=
                negb (source.(Account.balance) =? 0);
              SelfDestructResult.target_exists := target_exists;
              SelfDestructResult.previously_destroyed :=
                previously_destroyed |};
         StateLoad.is_cold := false |}, host).

  Definition block_hash (host : t) (number : u64) :
      option aliases.B256.t * t :=
    (option_map
      (fun value =>
        Impl_From_U256_for_FixedBytes_32.from (rust_word value))
      (lookup_z number.(M.Integer.value)
        host.(input).(Input.block).(Environment.Block.hashes)), host).

  Global Instance HostForRevmHost :
      @Host.C t IsLink host_types HostTypesAreLinks :=
    {| Host.TransactionGetter_for_Self := TransactionGetterForHost;
       Host.BlockGetter_for_Self := BlockGetterForHost;
       Host.CfgGetter_for_Self := CfgGetterForHost;
       Host.load_account_info_skip_cold_load self address _ skip_cold_load :=
         load_account_info_skip_cold_load self address skip_cold_load;
       Host.load_account_delegated := load_account_delegated;
       Host.load_account_code := load_account_code;
       Host.block_hash := block_hash;
       Host.max_initcode_size self :=
         ({| M.Integer.value := 49152 |}, self);
       Host.beneficiary self :=
         (rust_address self.(input).(Input.block).(Environment.Block.coinbase), self);
       Host.block_number self :=
         (rust_word self.(input).(Input.block).(Environment.Block.number), self);
       Host.timestamp self :=
         (rust_word self.(input).(Input.block).(Environment.Block.timestamp), self);
       Host.gas_limit self :=
         (rust_word self.(input).(Input.block).(Environment.Block.gas_limit), self);
       Host.chain_id self :=
         (rust_word
            self.(input).(Input.transaction).(Environment.Transaction.chain_id), self);
       Host.basefee self :=
         (rust_word self.(input).(Input.block).(Environment.Block.base_fee), self);
       Host.blob_gasprice self :=
         (rust_word self.(input).(Input.block).(Environment.Block.blob_base_fee), self);
       Host.effective_gas_price self :=
         (rust_word
            self.(input).(Input.transaction).(Environment.Transaction.gas_price), self);
       Host.caller self :=
         (rust_address self.(input).(Input.call).(Environment.Call.caller), self);
       Host.blob_hash self number :=
         (option_map rust_word
            (nth_error
              self.(input).(Input.transaction).(Environment.Transaction.blob_hashes)
              (Z.to_nat number.(M.Integer.value))), self);
       Host.difficulty self :=
         (rust_word self.(input).(Input.block).(Environment.Block.difficulty), self);
       Host.prevrandao self :=
         (option_map rust_word
            self.(input).(Input.block).(Environment.Block.previous_randao), self);
       Host.balance := balance;
       Host.code := code;
       Host.code_hash := code_hash;
       Host.sload := sload;
       Host.sload_skip_cold_load self address key skip_cold :=
         sload_skip_cold_load self address key skip_cold;
       Host.sstore := sstore;
       Host.sstore_skip_cold_load self address key value skip_cold :=
         sstore_skip_cold_load self address key value skip_cold;
       Host.tload := tload;
       Host.tstore := tstore;
       Host.log self entry := append_log self entry;
       Host.selfdestruct self address target _ :=
         selfdestruct self address target |}.
End StatefulHost.
Export (hints) StatefulHost.
