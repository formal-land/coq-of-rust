#[derive(Default)]
struct Mapping<K, V> {
    _key: core::marker::PhantomData<K>,
    _value: core::marker::PhantomData<V>,
}

impl<K, V> Mapping<K, V> {
    fn contains(&self, _key: &K) -> bool {
        unimplemented!()
    }

    fn get(&self, _key: &K) -> Option<V> {
        unimplemented!()
    }

    fn insert(&mut self, _key: K, _value: V) -> Option<u32> {
        unimplemented!()
    }

    fn remove(&self, _key: K) {
        unimplemented!()
    }

    fn size(&self, _key: K) -> Option<u32> {
        unimplemented!()
    }

    fn take(&self, _key: K) -> Option<V> {
        unimplemented!()
    }
}

#[derive(Default, Clone, Copy, PartialEq)]
struct AccountId(u128);

impl std::convert::From<[u8; 32]> for AccountId {
    fn from(_v: [u8; 32]) -> Self {
        unimplemented!()
    }
}

type Balance = u128;

struct Env {
    caller: AccountId,
}

/// Helper for referencing the zero address (`0x00`). Note that in practice this
/// address should not be treated in any special way (such as a default
/// placeholder) since it has a known private key.
fn zero_address() -> AccountId {
    [0u8; 32].into()
}

const ON_ERC_1155_RECEIVED_SELECTOR: [u8; 4] = [0xF2, 0x3A, 0x6E, 0x61];

// This is the return value that we expect if a smart contract supports batch receiving
// ERC-1155 tokens.
//
// It is calculated with
// `bytes4(keccak256("onERC1155BatchReceived(address,address,uint256[],uint256[],bytes)"
// ))`, and corresponds to 0xbc197c81.
const _ON_ERC_1155_BATCH_RECEIVED_SELECTOR: [u8; 4] = [0xBC, 0x19, 0x7C, 0x81];

/// A type representing the unique IDs of tokens managed by this contract.
pub type TokenId = u128;

// The ERC-1155 error types.
#[derive(PartialEq, Eq)]
pub enum Error {
    /// This token ID has not yet been created by the contract.
    UnexistentToken,
    /// The caller tried to sending tokens to the zero-address (`0x00`).
    ZeroAddressTransfer,
    /// The caller is not approved to transfer tokens on behalf of the account.
    NotApproved,
    /// The account does not have enough funds to complete the transfer.
    InsufficientBalance,
    /// An account does not need to approve themselves to transfer tokens.
    SelfApproval,
    /// The number of tokens being transferred does not match the specified number of
    /// transfers.
    BatchTransferMismatch,
}

// The ERC-1155 result types.
pub type Result<T> = core::result::Result<T, Error>;

/// Evaluate `$x:expr` and if not true return `Err($y:expr)`.
///
/// Used as `ensure!(expression_to_ensure, expression_to_return_on_false)`.
macro_rules! ensure {
    ( $condition:expr, $error:expr $(,)? ) => {{
        if !$condition {
            return Result::Err(core::convert::Into::into($error));
        }
    }};
}

/// The interface for an ERC-1155 compliant contract.
///
/// The interface is defined here: <https://eips.ethereum.org/EIPS/eip-1155>.
///
/// The goal of ERC-1155 is to allow a single contract to manage a variety of assets.
/// These assets can be fungible, non-fungible, or a combination.
///
/// By tracking multiple assets the ERC-1155 standard is able to support batch transfers,
/// which make it easy to transfer a mix of multiple tokens at once.
pub trait Erc1155 {
    /// Transfer a `value` amount of `token_id` tokens to the `to` account from the `from`
    /// account.
    ///
    /// Note that the call does not have to originate from the `from` account, and may
    /// originate from any account which is approved to transfer `from`'s tokens.
    fn safe_transfer_from(
        &mut self,
        from: AccountId,
        to: AccountId,
        token_id: TokenId,
        value: Balance,
        data: Vec<u8>,
    ) -> Result<()>;

    /// Perform a batch transfer of `token_ids` to the `to` account from the `from`
    /// account.
    ///
    /// The number of `values` specified to be transferred must match the number of
    /// `token_ids`, otherwise this call will revert.
    ///
    /// Note that the call does not have to originate from the `from` account, and may
    /// originate from any account which is approved to transfer `from`'s tokens.
    fn safe_batch_transfer_from(
        &mut self,
        from: AccountId,
        to: AccountId,
        token_ids: Vec<TokenId>,
        values: Vec<Balance>,
        data: Vec<u8>,
    ) -> Result<()>;

    /// Query the balance of a specific token for the provided account.
    fn balance_of(&self, owner: AccountId, token_id: TokenId) -> Balance;

    /// Query the balances for a set of tokens for a set of accounts.
    ///
    /// E.g use this call if you want to query what Alice and Bob's balances are for
    /// Tokens ID 1 and ID 2.
    ///
    /// This will return all the balances for a given owner before moving on to the next
    /// owner. In the example above this means that the return value should look like:
    ///
    /// [Alice Balance of Token ID 1, Alice Balance of Token ID 2, Bob Balance of Token ID
    /// 1, Bob Balance of Token ID 2]
    fn balance_of_batch(&self, owners: Vec<AccountId>, token_ids: Vec<TokenId>) -> Vec<Balance>;

    /// Enable or disable a third party, known as an `operator`, to control all tokens on
    /// behalf of the caller.
    fn set_approval_for_all(&mut self, operator: AccountId, approved: bool) -> Result<()>;

    /// Query if the given `operator` is allowed to control all of `owner`'s tokens.
    fn is_approved_for_all(&self, owner: AccountId, operator: AccountId) -> bool;
}

/// The interface for an ERC-1155 Token Receiver contract.
///
/// The interface is defined here: <https://eips.ethereum.org/EIPS/eip-1155>.
///
/// Smart contracts which want to accept token transfers must implement this interface. By
/// default if a contract does not support this interface any transactions originating
/// from an ERC-1155 compliant contract which attempt to transfer tokens directly to the
/// contract's address must be reverted.
pub trait Erc1155TokenReceiver {
    /// Handle the receipt of a single ERC-1155 token.
    ///
    /// This should be called by a compliant ERC-1155 contract if the intended recipient
    /// is a smart contract.
    ///
    /// If the smart contract implementing this interface accepts token transfers then it
    /// must return `ON_ERC_1155_RECEIVED_SELECTOR` from this function. To reject a
    /// transfer it must revert.
    ///
    /// Any callers must revert if they receive anything other than
    /// `ON_ERC_1155_RECEIVED_SELECTOR` as a return value.
    fn on_received(
        &mut self,
        operator: AccountId,
        from: AccountId,
        token_id: TokenId,
        value: Balance,
        data: Vec<u8>,
    ) -> Vec<u8>;

    /// Handle the receipt of multiple ERC-1155 tokens.
    ///
    /// This should be called by a compliant ERC-1155 contract if the intended recipient
    /// is a smart contract.
    ///
    /// If the smart contract implementing this interface accepts token transfers then it
    /// must return `BATCH_ON_ERC_1155_RECEIVED_SELECTOR` from this function. To
    /// reject a transfer it must revert.
    ///
    /// Any callers must revert if they receive anything other than
    /// `BATCH_ON_ERC_1155_RECEIVED_SELECTOR` as a return value.
    fn on_batch_received(
        &mut self,
        operator: AccountId,
        from: AccountId,
        token_ids: Vec<TokenId>,
        values: Vec<Balance>,
        data: Vec<u8>,
    ) -> Vec<u8>;
}

type Owner = AccountId;
type Operator = AccountId;

/// Indicate that a token transfer has occured.
///
/// This must be emitted even if a zero value transfer occurs.
pub struct TransferSingle {
    operator: Option<AccountId>,
    from: Option<AccountId>,
    to: Option<AccountId>,
    token_id: TokenId,
    value: Balance,
}

/// Indicate that an approval event has happened.
pub struct ApprovalForAll {
    owner: AccountId,
    operator: AccountId,
    approved: bool,
}

/// Indicate that a token's URI has been updated.
pub struct Uri {
    value: String,
    token_id: TokenId,
}

enum Event {
    TransferSingle(TransferSingle),
    ApprovalForAll(ApprovalForAll),
    Uri(Uri),
}

impl Env {
    fn caller(&self) -> AccountId {
        self.caller
    }

    fn emit_event(&self, _event: Event) {
        unimplemented!()
    }
}

/// An ERC-1155 contract.
#[derive(Default)]
pub struct Contract {
    /// Tracks the balances of accounts across the different tokens that they might
    /// be holding.
    balances: Mapping<(AccountId, TokenId), Balance>,
    /// Which accounts (called operators) have been approved to spend funds on behalf
    /// of an owner.
    approvals: Mapping<(Owner, Operator), ()>,
    /// A unique identifier for the tokens which have been minted (and are therefore
    /// supported) by this contract.
    token_id_nonce: TokenId,
}

impl Contract {
    fn init_env() -> Env {
        unimplemented!()
    }

    fn env(&self) -> Env {
        Self::init_env()
    }

    /// Initialize a default instance of this ERC-1155 implementation.
    pub fn new() -> Self {
        Default::default()
    }

    /// Create the initial supply for a token.
    ///
    /// The initial supply will be provided to the caller (a.k.a the minter), and the
    /// `token_id` will be assigned by the smart contract.
    ///
    /// Note that as implemented anyone can create tokens. If you were to instantiate
    /// this contract in a production environment you'd probably want to lock down
    /// the addresses that are allowed to create tokens.
    pub fn create(&mut self, value: Balance) -> TokenId {
        let caller = self.env().caller();

        // Given that TokenId is a `u128` the likelihood of this overflowing is pretty
        // slim.
        self.token_id_nonce += 1;
        self.balances.insert((caller, self.token_id_nonce), value);

        // Emit transfer event but with mint semantics
        self.env().emit_event(Event::TransferSingle(TransferSingle {
            operator: Some(caller),
            from: None,
            to: if value == 0 { None } else { Some(caller) },
            token_id: self.token_id_nonce,
            value,
        }));

        self.token_id_nonce
    }

    /// Mint a `value` amount of `token_id` tokens.
    ///
    /// It is assumed that the token has already been `create`-ed. The newly minted
    /// supply will be assigned to the caller (a.k.a the minter).
    ///
    /// Note that as implemented anyone can mint tokens. If you were to instantiate
    /// this contract in a production environment you'd probably want to lock down
    /// the addresses that are allowed to mint tokens.
    pub fn mint(&mut self, token_id: TokenId, value: Balance) -> Result<()> {
        ensure!(token_id <= self.token_id_nonce, Error::UnexistentToken);

        let caller = self.env().caller();
        self.balances.insert((caller, token_id), value);

        // Emit transfer event but with mint semantics
        self.env().emit_event(Event::TransferSingle(TransferSingle {
            operator: Some(caller),
            from: None,
            to: Some(caller),
            token_id,
            value,
        }));

        Ok(())
    }

    // Helper function for performing single token transfers.
    //
    // Should not be used directly since it's missing certain checks which are
    // important to the ERC-1155 standard (it is expected that the caller has
    // already performed these).
    //
    // # Panics
    //
    // If `from` does not hold any `token_id` tokens.
    fn perform_transfer(
        &mut self,
        from: AccountId,
        to: AccountId,
        token_id: TokenId,
        value: Balance,
    ) {
        let mut sender_balance = self
            .balances
            .get(&(from, token_id))
            .expect("Caller should have ensured that `from` holds `token_id`.");
        sender_balance -= value;
        self.balances.insert((from, token_id), sender_balance);

        let mut recipient_balance = self.balances.get(&(to, token_id)).unwrap_or(0 as u128);
        recipient_balance += value;
        self.balances.insert((to, token_id), recipient_balance);

        let caller = self.env().caller();
        self.env().emit_event(Event::TransferSingle(TransferSingle {
            operator: Some(caller),
            from: Some(from),
            to: Some(to),
            token_id,
            value,
        }));
    }

    // Check if the address at `to` is a smart contract which accepts ERC-1155 token
    // transfers.
    //
    // If they're a smart contract which **doesn't** accept tokens transfers this call
    // will revert. Otherwise we risk locking user funds at in that contract
    // with no chance of recovery.
    #[cfg_attr(test, allow(unused_variables))]
    fn transfer_acceptance_check(
        &mut self,
        caller: AccountId,
        from: AccountId,
        to: AccountId,
        token_id: TokenId,
        value: Balance,
        data: Vec<u8>,
    ) {
        // This is disabled during tests due to the use of `invoke_contract()` not
        // being supported (tests end up panicking).
        #[cfg(not(test))]
        {
            use ink::env::call::{build_call, ExecutionInput, Selector};

            // If our recipient is a smart contract we need to see if they accept or
            // reject this transfer. If they reject it we need to revert the call.
            let result = build_call::<Environment>()
                .call(to)
                .gas_limit(5000)
                .exec_input(
                    ExecutionInput::new(Selector::new(ON_ERC_1155_RECEIVED_SELECTOR))
                        .push_arg(caller)
                        .push_arg(from)
                        .push_arg(token_id)
                        .push_arg(value)
                        .push_arg(data),
                )
                .returns::<Vec<u8>>()
                .params()
                .try_invoke();

            match result {
                Ok(v) => {
                    ink::env::debug_println!(
                        "Received return value \"{:?}\" from contract {:?}",
                        v.clone()
                            .expect("Call should be valid, don't expect a `LangError`."),
                        from
                    );
                    assert_eq!(
                        v.clone()
                            .expect("Call should be valid, don't expect a `LangError`."),
                        &ON_ERC_1155_RECEIVED_SELECTOR[..],
                        "The recipient contract at {to:?} does not accept token transfers.\n
                            Expected: {ON_ERC_1155_RECEIVED_SELECTOR:?}, Got {v:?}"
                    )
                }
                Err(e) => {
                    match e {
                        ink::env::Error::CodeNotFound | ink::env::Error::NotCallable => {
                            // Our recipient wasn't a smart contract, so there's
                            // nothing more for
                            // us to do
                            ink::env::debug_println!(
                                "Recipient at {:?} from is not a smart contract ({:?})",
                                from,
                                e
                            );
                        }
                        _ => {
                            // We got some sort of error from the call to our
                            // recipient smart
                            // contract, and as such we must revert this call
                            panic!("Got error \"{e:?}\" while trying to call {from:?}")
                        }
                    }
                }
            }
        }
    }
}

impl Erc1155 for Contract {
    fn is_approved_for_all(&self, owner: AccountId, operator: AccountId) -> bool {
        self.approvals.contains(&(owner, operator))
    }

    fn balance_of(&self, owner: AccountId, token_id: TokenId) -> Balance {
        self.balances.get(&(owner, token_id)).unwrap_or(0 as u128)
    }

    fn safe_transfer_from(
        &mut self,
        from: AccountId,
        to: AccountId,
        token_id: TokenId,
        value: Balance,
        data: Vec<u8>,
    ) -> Result<()> {
        let caller = self.env().caller();
        if caller != from {
            ensure!(self.is_approved_for_all(from, caller), Error::NotApproved);
        }

        ensure!(to != zero_address(), Error::ZeroAddressTransfer);

        let balance = self.balance_of(from, token_id);
        ensure!(balance >= value, Error::InsufficientBalance);

        self.perform_transfer(from, to, token_id, value);
        self.transfer_acceptance_check(caller, from, to, token_id, value, data);

        Ok(())
    }

    fn safe_batch_transfer_from(
        &mut self,
        from: AccountId,
        to: AccountId,
        token_ids: Vec<TokenId>,
        values: Vec<Balance>,
        data: Vec<u8>,
    ) -> Result<()> {
        let caller = self.env().caller();
        if caller != from {
            ensure!(self.is_approved_for_all(from, caller), Error::NotApproved);
        }

        ensure!(to != zero_address(), Error::ZeroAddressTransfer);
        ensure!(!token_ids.is_empty(), Error::BatchTransferMismatch);
        ensure!(
            token_ids.len() == values.len(),
            Error::BatchTransferMismatch,
        );

        let transfers = token_ids.iter().zip(values.iter());
        for (&id, &v) in transfers.clone() {
            let balance = self.balance_of(from, id);
            ensure!(balance >= v, Error::InsufficientBalance);
        }

        for (&id, &v) in transfers {
            self.perform_transfer(from, to, id, v);
        }

        // Can use the any token ID/value here, we really just care about knowing if
        // `to` is a smart contract which accepts transfers
        self.transfer_acceptance_check(caller, from, to, token_ids[0], values[0], data);

        Ok(())
    }

    fn balance_of_batch(&self, owners: Vec<AccountId>, token_ids: Vec<TokenId>) -> Vec<Balance> {
        let mut output = Vec::new();
        for o in &owners {
            for t in &token_ids {
                let amount = self.balance_of(*o, *t);
                output.push(amount);
            }
        }
        output
    }

    fn set_approval_for_all(&mut self, operator: AccountId, approved: bool) -> Result<()> {
        let caller = self.env().caller();
        ensure!(operator != caller, Error::SelfApproval);

        if approved {
            self.approvals.insert((caller, operator), ());
        } else {
            self.approvals.remove((caller, operator));
        }

        self.env().emit_event(Event::ApprovalForAll(ApprovalForAll {
            owner: caller,
            operator,
            approved,
        }));

        Ok(())
    }
}

impl Erc1155TokenReceiver for Contract {
    fn on_received(
        &mut self,
        _operator: AccountId,
        _from: AccountId,
        _token_id: TokenId,
        _value: Balance,
        _data: Vec<u8>,
    ) -> Vec<u8> {
        // The ERC-1155 standard dictates that if a contract does not accept token
        // transfers directly to the contract, then the contract must
        // revert.
        //
        // This prevents a user from unintentionally transferring tokens to a smart
        // contract and getting their funds stuck without any sort of
        // recovery mechanism.
        //
        // Note that the choice of whether or not to accept tokens is implementation
        // specific, and we've decided to not accept them in this
        // implementation.
        unimplemented!("This smart contract does not accept token transfer.")
    }

    fn on_batch_received(
        &mut self,
        _operator: AccountId,
        _from: AccountId,
        _token_ids: Vec<TokenId>,
        _values: Vec<Balance>,
        _data: Vec<u8>,
    ) -> Vec<u8> {
        // The ERC-1155 standard dictates that if a contract does not accept token
        // transfers directly to the contract, then the contract must
        // revert.
        //
        // This prevents a user from unintentionally transferring tokens to a smart
        // contract and getting their funds stuck without any sort of
        // recovery mechanism.
        //
        // Note that the choice of whether or not to accept tokens is implementation
        // specific, and we've decided to not accept them in this
        // implementation.
        unimplemented!("This smart contract does not accept batch token transfers.")
    }
}
