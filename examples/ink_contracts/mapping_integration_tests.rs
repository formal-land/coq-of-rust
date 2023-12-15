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

    fn new() -> Mapping<K, V> {
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

#[derive(Default, Clone, Copy)]
struct AccountId(u128);

type Balance = u128;

struct Env {
    caller: AccountId,
}

impl Env {
    fn caller(&self) -> AccountId {
        self.caller
    }
}

/// A contract for testing `Mapping` functionality.
#[derive(Default)]
pub struct Mappings {
    /// Mapping from owner to number of owned token.
    balances: Mapping<AccountId, Balance>,
}

impl Mappings {
    fn init_env() -> Env {
        unimplemented!()
    }

    fn env() -> Env {
        unimplemented!()
    }

    /// Demonstrates the usage of `Mappings::default()`
    ///
    /// Creates an empty mapping between accounts and balances.
    pub fn new() -> Self {
        let balances = Mapping::default();
        Self { balances }
    }

    /// Demonstrates the usage of `Mapping::get()`.
    ///
    /// Returns the balance of a account, or `None` if the account is not in the
    /// `Mapping`.
    pub fn get_balance(&self) -> Option<Balance> {
        let caller = Self::env().caller();
        self.balances.get(&caller)
    }

    /// Demonstrates the usage of `Mappings::insert()`.
    ///
    /// Assigns the value to a given account.
    ///
    /// Returns the size of the pre-existing balance at the specified key if any.
    /// Returns `None` if the account was not previously in the `Mapping`.
    pub fn insert_balance(&mut self, value: Balance) -> Option<u32> {
        let caller = Self::env().caller();
        self.balances.insert(caller, value)
    }

    /// Demonstrates the usage of `Mappings::size()`.
    ///
    /// Returns the size of the pre-existing balance at the specified key if any.
    /// Returns `None` if the account was not previously in the `Mapping`.
    pub fn size_balance(&mut self) -> Option<u32> {
        let caller = Self::env().caller();
        self.balances.size(caller)
    }

    /// Demonstrates the usage of `Mapping::contains()`.
    ///
    /// Returns `true` if the account has any balance assigned to it.
    pub fn contains_balance(&self) -> bool {
        let caller = Self::env().caller();
        self.balances.contains(&caller)
    }

    /// Demonstrates the usage of `Mappings::remove()`.
    ///
    /// Removes the balance entry for a given account.
    pub fn remove_balance(&mut self) {
        let caller = Self::env().caller();
        self.balances.remove(caller);
    }

    /// Demonstrates the usage of `Mappings::take()`.
    ///
    /// Returns the balance of a given account removing it from storage.
    ///
    /// Returns `None` if the account is not in the `Mapping`.
    pub fn take_balance(&mut self) -> Option<Balance> {
        let caller = Self::env().caller();
        self.balances.take(caller)
    }
}
