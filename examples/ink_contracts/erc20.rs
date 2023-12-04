#[derive(Default)]
struct Mapping<K, V> {
    _key: core::marker::PhantomData<K>,
    _value: core::marker::PhantomData<V>,
}

impl<K, V> Mapping<K, V> {
    fn get(&self, _key: &K) -> Option<V> {
        unimplemented!()
    }

    fn insert(&mut self, _key: K, _value: V) {
        unimplemented!()
    }
}

#[derive(Default, Clone, Copy)]
struct AccountId(u128);

type Balance = u128;

struct Env {
    caller: AccountId,
}

/// A simple ERC-20 contract.
// #[ink(storage)]
#[derive(Default)]
struct Erc20 {
    /// Total token supply.
    total_supply: Balance,
    /// Mapping from owner to number of owned token.
    balances: Mapping<AccountId, Balance>,
    /// Mapping of the token amount which an account is allowed to withdraw
    /// from another account.
    allowances: Mapping<(AccountId, AccountId), Balance>,
}

/// Event emitted when a token transfer occurs.
// #[ink(event)]
struct Transfer {
    // #[ink(topic)]
    from: Option<AccountId>,
    // #[ink(topic)]
    to: Option<AccountId>,
    value: Balance,
}

/// Event emitted when an approval occurs that `spender` is allowed to withdraw
/// up to the amount of `value` tokens from `owner`.
// #[ink(event)]
struct Approval {
    // #[ink(topic)]
    owner: AccountId,
    // #[ink(topic)]
    spender: AccountId,
    value: Balance,
}

/// The ERC-20 error types.
enum Error {
    /// Returned if not enough balance to fulfill a request is available.
    InsufficientBalance,
    /// Returned if not enough allowance to fulfill a request is available.
    InsufficientAllowance,
}

/// The ERC-20 result type.
type Result<T> = core::result::Result<T, Error>;

impl Env {
    fn caller(&self) -> AccountId {
        self.caller
    }

    fn emit_event<Event>(&self, _event: Event) {
        unimplemented!()
    }
}

impl Erc20 {
    fn init_env() -> Env {
        unimplemented!()
    }

    fn env(&self) -> Env {
        Self::init_env()
    }
}

impl Erc20 {
    /// Creates a new ERC-20 contract with the specified initial supply.
    // #[ink(constructor)]
    fn new(total_supply: Balance) -> Self {
        let mut balances = Mapping::default();
        let caller = Self::init_env().caller();
        balances.insert(caller, total_supply);
        Self::init_env().emit_event(Transfer {
            from: None,
            to: Some(caller),
            value: total_supply,
        });
        Self {
            total_supply,
            balances,
            allowances: Default::default(),
        }
    }

    /// Returns the total token supply.
    // #[ink(message)]
    fn total_supply(&self) -> Balance {
        self.total_supply
    }

    /// Returns the account balance for the specified `owner`.
    ///
    /// Returns `0` if the account is non-existent.
    ///
    /// # Note
    ///
    /// Prefer to call this method over `balance_of` since this
    /// works using references which are more efficient in Wasm.
    #[inline]
    fn balance_of_impl(&self, owner: &AccountId) -> Balance {
        self.balances.get(owner).unwrap_or_default()
    }

    /// Returns the account balance for the specified `owner`.
    ///
    /// Returns `0` if the account is non-existent.
    // #[ink(message)]
    fn balance_of(&self, owner: AccountId) -> Balance {
        self.balance_of_impl(&owner)
    }

    /// Returns the amount which `spender` is still allowed to withdraw from `owner`.
    ///
    /// Returns `0` if no allowance has been set.
    ///
    /// # Note
    ///
    /// Prefer to call this method over `allowance` since this
    /// works using references which are more efficient in Wasm.
    #[inline]
    fn allowance_impl(&self, owner: &AccountId, spender: &AccountId) -> Balance {
        self.allowances.get(&(*owner, *spender)).unwrap_or_default()
    }

    /// Returns the amount which `spender` is still allowed to withdraw from `owner`.
    ///
    /// Returns `0` if no allowance has been set.
    // #[ink(message)]
    fn allowance(&self, owner: AccountId, spender: AccountId) -> Balance {
        self.allowance_impl(&owner, &spender)
    }

    /// Transfers `value` amount of tokens from the caller's account to account `to`.
    ///
    /// On success a `Transfer` event is emitted.
    ///
    /// # Errors
    ///
    /// Returns `InsufficientBalance` error if there are not enough tokens on
    /// the caller's account balance.
    fn transfer_from_to(&mut self, from: &AccountId, to: &AccountId, value: Balance) -> Result<()> {
        let from_balance = self.balance_of_impl(from);
        if from_balance < value {
            return Err(Error::InsufficientBalance);
        }

        self.balances.insert(*from, from_balance - value);
        let to_balance = self.balance_of_impl(to);
        self.balances.insert(*to, to_balance + value);
        self.env().emit_event(Transfer {
            from: Some(*from),
            to: Some(*to),
            value,
        });
        Ok(())
    }

    /// Transfers `value` amount of tokens from the caller's account to account `to`.
    ///
    /// On success a `Transfer` event is emitted.
    ///
    /// # Errors
    ///
    /// Returns `InsufficientBalance` error if there are not enough tokens on
    /// the caller's account balance.
    // #[ink(message)]
    fn transfer(&mut self, to: AccountId, value: Balance) -> Result<()> {
        let from = self.env().caller();
        self.transfer_from_to(&from, &to, value)
    }

    /// Allows `spender` to withdraw from the caller's account multiple times, up to
    /// the `value` amount.
    ///
    /// If this function is called again it overwrites the current allowance with
    /// `value`.
    ///
    /// An `Approval` event is emitted.
    // #[ink(message)]
    fn approve(&mut self, spender: AccountId, value: Balance) -> Result<()> {
        let owner = self.env().caller();
        self.allowances.insert((owner, spender), value);
        self.env().emit_event(Approval {
            owner,
            spender,
            value,
        });
        Ok(())
    }

    /// Transfers `value` tokens on the behalf of `from` to the account `to`.
    ///
    /// This can be used to allow a contract to transfer tokens on ones behalf and/or
    /// to charge fees in sub-currencies, for example.
    ///
    /// On success a `Transfer` event is emitted.
    ///
    /// # Errors
    ///
    /// Returns `InsufficientAllowance` error if there are not enough tokens allowed
    /// for the caller to withdraw from `from`.
    ///
    /// Returns `InsufficientBalance` error if there are not enough tokens on
    /// the account balance of `from`.
    // #[ink(message)]
    fn transfer_from(&mut self, from: AccountId, to: AccountId, value: Balance) -> Result<()> {
        let caller = self.env().caller();
        let allowance = self.allowance_impl(&from, &caller);
        if allowance < value {
            return Err(Error::InsufficientAllowance);
        }
        self.transfer_from_to(&from, &to, value)?;
        self.allowances.insert((from, caller), allowance - value);
        Ok(())
    }
}
