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

impl From<[u8; 32]> for AccountId {
    fn from(_value: [u8; 32]) -> Self {
        unimplemented!()
    }
}

type Balance = u128;

struct Env {
    caller: AccountId,
}

/// A token ID.
pub type TokenId = u32;

#[derive(Default)]
pub struct Erc721 {
    /// Mapping from token to owner.
    token_owner: Mapping<TokenId, AccountId>,
    /// Mapping from token to approvals users.
    token_approvals: Mapping<TokenId, AccountId>,
    /// Mapping from owner to number of owned token.
    owned_tokens_count: Mapping<AccountId, u32>,
    /// Mapping from owner to operator approvals.
    operator_approvals: Mapping<(AccountId, AccountId), ()>,
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Error {
    NotOwner,
    NotApproved,
    TokenExists,
    TokenNotFound,
    CannotInsert,
    CannotFetchValue,
    NotAllowed,
}

/// Event emitted when a token transfer occurs.
pub struct Transfer {
    from: Option<AccountId>,
    to: Option<AccountId>,
    id: TokenId,
}

/// Event emitted when a token approve occurs.
pub struct Approval {
    from: AccountId,
    to: AccountId,
    id: TokenId,
}

/// Event emitted when an operator is enabled or disabled for an owner.
/// The operator can manage all NFTs of the owner.
pub struct ApprovalForAll {
    owner: AccountId,
    operator: AccountId,
    approved: bool,
}

enum Event {
    Transfer(Transfer),
    Approval(Approval),
    ApprovalForAll(ApprovalForAll),
}

impl Env {
    fn caller(&self) -> AccountId {
        self.caller
    }

    fn emit_event(&self, _event: Event) {
        unimplemented!()
    }
}

impl Erc721 {
    fn init_env() -> Env {
        unimplemented!()
    }

    fn env(&self) -> Env {
        Self::init_env()
    }

    /// Creates a new ERC-721 token contract.
    pub fn new() -> Self {
        Default::default()
    }

    // Returns the total number of tokens from an account.
    fn balance_of_or_zero(&self, of: &AccountId) -> u32 {
        self.owned_tokens_count.get(of).unwrap_or(0 as u32)
    }

    /// Removes existing approval from token `id`.
    fn clear_approval(&mut self, id: TokenId) {
        self.token_approvals.remove(id);
    }

    /// Gets an operator on other Account's behalf.
    fn approved_for_all(&self, owner: AccountId, operator: AccountId) -> bool {
        self.operator_approvals.contains(&(owner, operator))
    }

    /// Returns the owner of the token.
    pub fn owner_of(&self, id: TokenId) -> Option<AccountId> {
        self.token_owner.get(&id)
    }

    /// Returns true if the `AccountId` `from` is the owner of token `id`
    /// or it has been approved on behalf of the token `id` owner.
    fn approved_or_owner(&self, from: Option<AccountId>, id: TokenId) -> bool {
        let owner = self.owner_of(id);
        from != Some(AccountId::from([0x0; 32]))
            && (from == owner
                || from == self.token_approvals.get(&id)
                || self.approved_for_all(
                    owner.expect("Error with AccountId"),
                    from.expect("Error with AccountId"),
                ))
    }

    /// Returns true if token `id` exists or false if it does not.
    fn exists(&self, id: TokenId) -> bool {
        self.token_owner.contains(&id)
    }

    /// Returns the balance of the owner.
    ///
    /// This represents the amount of unique tokens the owner has.
    pub fn balance_of(&self, owner: AccountId) -> u32 {
        self.balance_of_or_zero(&owner)
    }

    /// Returns the approved account ID for this token if any.
    pub fn get_approved(&self, id: TokenId) -> Option<AccountId> {
        self.token_approvals.get(&id)
    }

    /// Returns `true` if the operator is approved by the owner.
    pub fn is_approved_for_all(&self, owner: AccountId, operator: AccountId) -> bool {
        self.approved_for_all(owner, operator)
    }

    /// Approves or disapproves the operator to transfer all tokens of the caller.
    fn approve_for_all(&mut self, to: AccountId, approved: bool) -> Result<(), Error> {
        let caller = self.env().caller();
        if to == caller {
            return Err(Error::NotAllowed);
        }
        self.env().emit_event(Event::ApprovalForAll(ApprovalForAll {
            owner: caller,
            operator: to,
            approved,
        }));

        if approved {
            self.operator_approvals.insert((caller, to), ());
        } else {
            self.operator_approvals.remove((caller, to));
        }

        Ok(())
    }

    /// Approves or disapproves the operator for all tokens of the caller.
    pub fn set_approval_for_all(&mut self, to: AccountId, approved: bool) -> Result<(), Error> {
        self.approve_for_all(to, approved)?;
        Ok(())
    }

    /// Approve the passed `AccountId` to transfer the specified token on behalf of
    /// the message's sender.
    fn approve_for(&mut self, to: &AccountId, id: TokenId) -> Result<(), Error> {
        let caller = self.env().caller();
        let owner = self.owner_of(id);
        if !(owner == Some(caller)
            || self.approved_for_all(owner.expect("Error with AccountId"), caller))
        {
            return Err(Error::NotAllowed);
        };

        if *to == AccountId::from([0x0; 32]) {
            return Err(Error::NotAllowed);
        };

        if self.token_approvals.contains(&id) {
            return Err(Error::CannotInsert);
        } else {
            self.token_approvals.insert(id, *to);
        }

        self.env().emit_event(Event::Approval(Approval {
            from: caller,
            to: *to,
            id,
        }));

        Ok(())
    }

    /// Approves the account to transfer the specified token on behalf of the caller.
    pub fn approve(&mut self, to: AccountId, id: TokenId) -> Result<(), Error> {
        self.approve_for(&to, id)?;
        Ok(())
    }

    /// Removes token `id` from the owner.
    #[allow(unknown_lints)]
    #[allow(coq_axiom)]
    fn remove_token_from(&mut self, from: &AccountId, id: TokenId) -> Result<(), Error> {
        let Self {
            token_owner,
            owned_tokens_count,
            ..
        } = self;

        if !token_owner.contains(&id) {
            return Err(Error::TokenNotFound);
        }

        let count = owned_tokens_count
            .get(from)
            .map(|c| c - (1 as u32))
            .ok_or(Error::CannotFetchValue)?;
        owned_tokens_count.insert(*from, count);
        token_owner.remove(id);

        Ok(())
    }

    /// Adds the token `id` to the `to` AccountID.
    #[allow(unknown_lints)]
    #[allow(coq_axiom)]
    fn add_token_to(&mut self, to: &AccountId, id: TokenId) -> Result<(), Error> {
        let Self {
            token_owner,
            owned_tokens_count,
            ..
        } = self;

        if token_owner.contains(&id) {
            return Err(Error::TokenExists);
        }

        if *to == AccountId::from([0x0; 32]) {
            return Err(Error::NotAllowed);
        };

        let count = owned_tokens_count
            .get(to)
            .map(|c| c + (1 as u32))
            .unwrap_or(1);

        owned_tokens_count.insert(*to, count);
        token_owner.insert(id, *to);

        Ok(())
    }

    /// Transfers token `id` `from` the sender to the `to` `AccountId`.
    #[allow(unknown_lints)]
    #[allow(coq_axiom)]
    fn transfer_token_from(
        &mut self,
        from: &AccountId,
        to: &AccountId,
        id: TokenId,
    ) -> Result<(), Error> {
        let caller = self.env().caller();
        if !self.exists(id) {
            return Err(Error::TokenNotFound);
        };
        if !self.approved_or_owner(Some(caller), id) {
            return Err(Error::NotApproved);
        };
        self.clear_approval(id);
        self.remove_token_from(from, id)?;
        self.add_token_to(to, id)?;
        self.env().emit_event(Event::Transfer(Transfer {
            from: Some(*from),
            to: Some(*to),
            id,
        }));
        Ok(())
    }

    /// Transfers the token from the caller to the given destination.
    pub fn transfer(&mut self, destination: AccountId, id: TokenId) -> Result<(), Error> {
        let caller = self.env().caller();
        self.transfer_token_from(&caller, &destination, id)?;
        Ok(())
    }

    /// Transfer approved or owned token.
    pub fn transfer_from(
        &mut self,
        from: AccountId,
        to: AccountId,
        id: TokenId,
    ) -> Result<(), Error> {
        self.transfer_token_from(&from, &to, id)?;
        Ok(())
    }

    /// Creates a new token.
    pub fn mint(&mut self, id: TokenId) -> Result<(), Error> {
        let caller = self.env().caller();
        self.add_token_to(&caller, id)?;
        self.env().emit_event(Event::Transfer(Transfer {
            from: Some(AccountId::from([0x0; 32])),
            to: Some(caller),
            id,
        }));
        Ok(())
    }

    /// Deletes an existing token. Only the owner can burn the token.
    #[allow(unknown_lints)]
    #[allow(coq_axiom)]
    pub fn burn(&mut self, id: TokenId) -> Result<(), Error> {
        let caller = self.env().caller();
        let Self {
            token_owner,
            owned_tokens_count,
            ..
        } = self;

        let owner = token_owner.get(&id).ok_or(Error::TokenNotFound)?;
        if owner != caller {
            return Err(Error::NotOwner);
        };

        let count = owned_tokens_count
            .get(&caller)
            .map(|c| c - 1)
            .ok_or(Error::CannotFetchValue)?;
        owned_tokens_count.insert(caller, count);
        token_owner.remove(id);

        self.env().emit_event(Event::Transfer(Transfer {
            from: Some(caller),
            to: Some(AccountId::from([0x0; 32])),
            id,
        }));

        Ok(())
    }
}
