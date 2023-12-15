#[derive(Default, Clone, Copy, Eq, PartialEq)]
struct AccountId(u128);

impl std::convert::From<[u8; 32]> for AccountId {
    fn from(value: [u8; 32]) -> Self {
        unimplemented!()
    }
}

type Balance = u128;

type Timestamp = u64;

struct Env {
    caller: AccountId,
}

/// Struct for storing the payment channel details.
/// The creator of the contract, i.e the `sender`, can deposit funds to the payment
/// channel while deploying the contract.
pub struct PaymentChannel {
    /// The `AccountId` of the sender of the payment channel.
    sender: AccountId,
    /// The `AccountId` of the recipient of the payment channel.
    recipient: AccountId,
    /// The `Timestamp` at which the contract expires. The field is optional.
    /// The contract never expires if set to `None`.
    expiration: Option<Timestamp>,
    /// The `Amount` withdrawn by the recipient.
    withdrawn: Balance,
    /// The `Timestamp` which will be added to the current time when the sender
    /// wishes to close the channel. This will be set at the time of contract
    /// instantiation.
    close_duration: Timestamp,
}

/// Errors that can occur upon calling this contract.
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// Returned if caller is not the `sender` while required to.
    CallerIsNotSender,
    /// Returned if caller is not the `recipient` while required to.
    CallerIsNotRecipient,
    /// Returned if the requested withdrawal amount is less than the amount
    /// that is already already withdrawn.
    AmountIsLessThanWithdrawn,
    /// Returned if the requested transfer failed. This can be the case if the
    /// contract does not have sufficient free funds or if the transfer would
    /// have brought the contract's balance below minimum balance.
    TransferFailed,
    /// Returned if the contract hasn't expired yet and the `sender` wishes to
    /// close the channel.
    NotYetExpired,
    /// Returned if the signature is invalid.
    InvalidSignature,
}

/// Type alias for the contract's `Result` type.
pub type Result<T> = core::result::Result<T, Error>;

/// Emitted when the sender starts closing the channel.
pub struct SenderCloseStarted {
    expiration: Timestamp,
    close_duration: Timestamp,
}

enum Event {
    SenderCloseStarted(SenderCloseStarted),
}

impl Env {
    fn caller(&self) -> AccountId {
        self.caller
    }

    fn emit_event(&self, _event: Event) {
        unimplemented!()
    }

    fn terminate_contract(&self, sender: AccountId) {
        unimplemented!()
    }

    fn transfer(&self, recipient: AccountId, amount: Balance) -> Result<()> {
        unimplemented!()
    }

    fn block_timestamp(&self) -> Timestamp {
        unimplemented!()
    }

    fn balance(&self) -> Balance {
        unimplemented!()
    }

    fn account_id(&self) -> AccountId {
        unimplemented!()
    }
}

impl PaymentChannel {
    fn init_env() -> Env {
        unimplemented!()
    }

    fn env(&self) -> Env {
        Self::init_env()
    }

    /// The only constructor of the contract.
    ///
    /// The arguments `recipient` and `close_duration` are required.
    ///
    /// `expiration` will be set to `None`, so that the contract will
    /// never expire. `sender` can call `start_sender_close` to override
    /// this. `sender` will be able to claim the remaining balance by calling
    /// `claim_timeout` after `expiration` has passed.
    pub fn new(recipient: AccountId, close_duration: Timestamp) -> Self {
        Self {
            sender: Self::init_env().caller(),
            recipient,
            expiration: None,
            withdrawn: 0,
            close_duration,
        }
    }

    /// The `recipient` can close the payment channel anytime. The specified
    /// `amount` will be sent to the `recipient` and the remainder will go
    /// back to the `sender`.
    pub fn close(&mut self, amount: Balance, signature: [u8; 65]) -> Result<()> {
        self.close_inner(amount, signature)?;
        self.env().terminate_contract(self.sender);

        Ok(())
    }

    /// We split this out in order to make testing `close` simpler.
    fn close_inner(&mut self, amount: Balance, signature: [u8; 65]) -> Result<()> {
        if self.env().caller() != self.recipient {
            return Err(Error::CallerIsNotRecipient);
        }

        if amount < self.withdrawn {
            return Err(Error::AmountIsLessThanWithdrawn);
        }

        // Signature validation
        if !self.is_signature_valid(amount, signature) {
            return Err(Error::InvalidSignature);
        }

        self.env()
            .transfer(self.recipient, amount - self.withdrawn)
            .map_err(|_| Error::TransferFailed)?;

        Ok(())
    }

    /// If the `sender` wishes to close the channel and withdraw the funds they can
    /// do so by setting the `expiration`. If the `expiration` is reached, the
    /// sender will be able to call `claim_timeout` to claim the remaining funds
    /// and the channel will be terminated. This emits an event that the recipient can
    /// listen to in order to withdraw the funds before the `expiration`.
    pub fn start_sender_close(&mut self) -> Result<()> {
        if self.env().caller() != self.sender {
            return Err(Error::CallerIsNotSender);
        }

        let now = self.env().block_timestamp();
        let expiration = now + self.close_duration;

        self.env()
            .emit_event(Event::SenderCloseStarted(SenderCloseStarted {
                expiration,
                close_duration: self.close_duration,
            }));

        self.expiration = Some(expiration);

        Ok(())
    }

    /// If the timeout is reached (`current_time >= expiration`) without the
    /// recipient closing the channel, then the remaining balance is released
    /// back to the `sender`.
    pub fn claim_timeout(&mut self) -> Result<()> {
        match self.expiration {
            Some(expiration) => {
                // expiration is set. Check if it's reached and if so, release the
                // funds and terminate the contract.
                let now = self.env().block_timestamp();
                if now < expiration {
                    return Err(Error::NotYetExpired);
                }

                self.env().terminate_contract(self.sender);

                Ok(())
            }

            None => Err(Error::NotYetExpired),
        }
    }

    /// The `recipient` can withdraw the funds from the channel at any time.
    pub fn withdraw(&mut self, amount: Balance, signature: [u8; 65]) -> Result<()> {
        if self.env().caller() != self.recipient {
            return Err(Error::CallerIsNotRecipient);
        }

        // Signature validation
        if !self.is_signature_valid(amount, signature) {
            return Err(Error::InvalidSignature);
        }

        // Make sure there's something to withdraw (guards against underflow)
        if amount < self.withdrawn {
            return Err(Error::AmountIsLessThanWithdrawn);
        }

        let amount_to_withdraw = amount - self.withdrawn;
        self.withdrawn += amount_to_withdraw;

        self.env()
            .transfer(self.recipient, amount_to_withdraw)
            .map_err(|_| Error::TransferFailed)?;

        Ok(())
    }

    /// Returns the `sender` of the contract.
    pub fn get_sender(&self) -> AccountId {
        self.sender
    }

    /// Returns the `recipient` of the contract.
    pub fn get_recipient(&self) -> AccountId {
        self.recipient
    }

    /// Returns the `expiration` of the contract.
    pub fn get_expiration(&self) -> Option<Timestamp> {
        self.expiration
    }

    /// Returns the `withdrawn` amount of the contract.
    pub fn get_withdrawn(&self) -> Balance {
        self.withdrawn
    }

    /// Returns the `close_duration` of the contract.
    pub fn get_close_duration(&self) -> Timestamp {
        self.close_duration
    }

    /// Returns the `balance` of the contract.
    pub fn get_balance(&self) -> Balance {
        self.env().balance()
    }
}

pub trait HashOutput {
    type Type: Default;
}

pub trait CryptoHash: HashOutput {
    // Required method
    fn hash(input: &[u8], output: &mut <Self as HashOutput>::Type);
}

pub fn hash_encoded<H, T>(input: &T, output: &mut <H as HashOutput>::Type)
where
    H: CryptoHash,
{
    unimplemented!()
}

pub fn ecdsa_recover(
    signature: &[u8; 65],
    message_hash: &[u8; 32],
    output: &mut [u8; 33],
) -> Result<()> {
    unimplemented!()
}

pub enum Sha2x256 {}

pub enum Keccak256 {}

pub enum Blake2x256 {}

pub enum Blake2x128 {}

impl HashOutput for Sha2x256 {
    type Type = [u8; 32];
}

impl HashOutput for Keccak256 {
    type Type = [u8; 32];
}

impl HashOutput for Blake2x256 {
    type Type = [u8; 32];
}

impl HashOutput for Blake2x128 {
    type Type = [u8; 16];
}

impl CryptoHash for Sha2x256 {
    fn hash(input: &[u8], output: &mut <Self as HashOutput>::Type) {
        unimplemented!()
    }
}

impl CryptoHash for Keccak256 {
    fn hash(input: &[u8], output: &mut <Self as HashOutput>::Type) {
        unimplemented!()
    }
}

impl CryptoHash for Blake2x256 {
    fn hash(input: &[u8], output: &mut <Self as HashOutput>::Type) {
        unimplemented!()
    }
}

impl CryptoHash for Blake2x128 {
    fn hash(input: &[u8], output: &mut <Self as HashOutput>::Type) {
        unimplemented!()
    }
}

impl PaymentChannel {
    fn is_signature_valid(&self, amount: Balance, signature: [u8; 65]) -> bool {
        let encodable = (self.env().account_id(), amount);
        let mut message = <Sha2x256 as HashOutput>::Type::default();
        hash_encoded::<Sha2x256, _>(&encodable, &mut message);

        let mut pub_key = [0; 33];
        ecdsa_recover(&signature, &message, &mut pub_key)
            .unwrap_or_else(|err| panic!("recover failed: {err:?}"));
        let mut signature_account_id = [0; 32];
        <Blake2x256 as CryptoHash>::hash(&pub_key, &mut signature_account_id);

        self.recipient == signature_account_id.into()
    }
}
