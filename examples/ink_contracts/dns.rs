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

#[derive(Default, Clone, Copy, PartialEq)]
struct AccountId(u128);

impl std::convert::From<[u8; 32]> for AccountId {
    fn from(_value: [u8; 32]) -> Self {
        unimplemented!()
    }
}

type Balance = u128;

type Hash = [u8; 32];

struct Env {
    caller: AccountId,
}

impl Env {
    fn caller(&self) -> AccountId {
        self.caller
    }

    fn emit_event(&self, _event: Event) {
        unimplemented!()
    }
}

/// Emitted whenever a new name is being registered.
pub struct Register {
    name: Hash,
    from: AccountId,
}

/// Emitted whenever an address changes.
pub struct SetAddress {
    name: Hash,
    from: AccountId,
    old_address: Option<AccountId>,
    new_address: AccountId,
}

/// Emitted whenever a name is being transferred.
pub struct Transfer {
    name: Hash,
    from: AccountId,
    old_owner: Option<AccountId>,
    new_owner: AccountId,
}

enum Event {
    Register(Register),
    SetAddress(SetAddress),
    Transfer(Transfer),
}

/// Domain name service contract inspired by
/// [this blog post](https://medium.com/@chainx_org/secure-and-decentralized-polkadot-domain-name-system-e06c35c2a48d).
///
/// # Note
///
/// This is a port from the blog post's ink! 1.0 based version of the contract
/// to ink! 2.0.
///
/// # Description
///
/// The main function of this contract is domain name resolution which
/// refers to the retrieval of numeric values corresponding to readable
/// and easily memorable names such as "polka.dot" which can be used
/// to facilitate transfers, voting and DApp-related operations instead
/// of resorting to long IP addresses that are hard to remember.
pub struct DomainNameService {
    /// A hashmap to store all name to addresses mapping.
    name_to_address: Mapping<Hash, AccountId>,
    /// A hashmap to store all name to owners mapping.
    name_to_owner: Mapping<Hash, AccountId>,
    /// The default address.
    default_address: AccountId,
}

impl Default for DomainNameService {
    fn default() -> Self {
        let mut name_to_address = Mapping::new();
        name_to_address.insert(Hash::default(), zero_address());
        let mut name_to_owner = Mapping::new();
        name_to_owner.insert(Hash::default(), zero_address());

        Self {
            name_to_address,
            name_to_owner,
            default_address: zero_address(),
        }
    }
}

/// Errors that can occur upon calling this contract.
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// Returned if the name already exists upon registration.
    NameAlreadyExists,
    /// Returned if caller is not owner while required to.
    CallerIsNotOwner,
}

/// Type alias for the contract's result type.
pub type Result<T> = core::result::Result<T, Error>;

impl DomainNameService {
    fn init_env() -> Env {
        unimplemented!()
    }

    fn env(&self) -> Env {
        Self::init_env()
    }

    /// Creates a new domain name service contract.
    pub fn new() -> Self {
        Default::default()
    }

    /// Register specific name with caller as owner.
    pub fn register(&mut self, name: Hash) -> Result<()> {
        let caller = self.env().caller();
        if self.name_to_owner.contains(&name) {
            return Err(Error::NameAlreadyExists);
        }

        self.name_to_owner.insert(name, caller);
        self.env()
            .emit_event(Event::Register(Register { name, from: caller }));

        Ok(())
    }

    /// Set address for specific name.
    pub fn set_address(&mut self, name: Hash, new_address: AccountId) -> Result<()> {
        let caller = self.env().caller();
        let owner = self.get_owner_or_default(name);
        if caller != owner {
            return Err(Error::CallerIsNotOwner);
        }

        let old_address = self.name_to_address.get(&name);
        self.name_to_address.insert(name, new_address);

        self.env().emit_event(Event::SetAddress(SetAddress {
            name,
            from: caller,
            old_address,
            new_address,
        }));
        Ok(())
    }

    /// Transfer owner to another address.
    pub fn transfer(&mut self, name: Hash, to: AccountId) -> Result<()> {
        let caller = self.env().caller();
        let owner = self.get_owner_or_default(name);
        if caller != owner {
            return Err(Error::CallerIsNotOwner);
        }

        let old_owner = self.name_to_owner.get(&name);
        self.name_to_owner.insert(name, to);

        self.env().emit_event(Event::Transfer(Transfer {
            name,
            from: caller,
            old_owner,
            new_owner: to,
        }));

        Ok(())
    }

    /// Get address for specific name.
    pub fn get_address(&self, name: Hash) -> AccountId {
        self.get_address_or_default(name)
    }

    /// Get owner of specific name.
    pub fn get_owner(&self, name: Hash) -> AccountId {
        self.get_owner_or_default(name)
    }

    /// Returns the owner given the hash or the default address.
    fn get_owner_or_default(&self, name: Hash) -> AccountId {
        self.name_to_owner
            .get(&name)
            .unwrap_or(self.default_address)
    }

    /// Returns the address given the hash or the default address.
    fn get_address_or_default(&self, name: Hash) -> AccountId {
        self.name_to_address
            .get(&name)
            .unwrap_or(self.default_address)
    }
}

/// Helper for referencing the zero address (`0x00`). Note that in practice this
/// address should not be treated in any special way (such as a default
/// placeholder) since it has a known private key.
fn zero_address() -> AccountId {
    [0u8; 32].into()
}
