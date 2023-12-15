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

#[derive(Default, Clone, Copy, Eq, PartialEq, Debug)]
struct AccountId(u128);

type Balance = u128;

type BlockNumber = u32;

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

/// Struct for storing winning bids per bidding sample (a block).
/// Vector index corresponds to sample number.
/// Wrapping vector, just added for testing UI components.
#[derive(Default, PartialEq, Eq, Debug, Clone)]
pub struct Bids(Vec<Vec<Option<(AccountId, Balance)>>>);

/// Auction outline.
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Outline {
    NoWinner,
    WinnerDetected,
    PayoutCompleted,
}

/// Auction statuses.
/// Logic inspired by
/// [Parachain Auction](https://github.com/paritytech/polkadot/blob/master/runtime/common/src/traits.rs#L160)
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Status {
    /// An auction has not started yet.
    NotStarted,
    /// We are in the starting period of the auction, collecting initial bids.
    OpeningPeriod,
    /// We are in the ending period of the auction, where we are taking snapshots of
    /// the winning bids. Snapshots are taken currently on per-block basis,
    /// but this logic could be later evolve to take snapshots of on
    /// arbitrary length (in blocks).
    EndingPeriod(BlockNumber),
    /// Candle was blown.
    Ended(Outline),
    /// We have completed the bidding process and are waiting for the Random Function
    /// to return some acceptable randomness to select the winner. The number
    /// represents how many blocks we have been waiting.
    RfDelay(BlockNumber),
}

/// Struct for storing auction data.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Auction {
    /// Branded name of the auction event.
    name: String,
    /// Some hash identifying the auction subject.
    subject: Hash,
    /// Structure storing the bids being made.
    bids: Bids,
    /// Auction terms encoded as:
    /// `[start_block, opening_period, closing_period]`
    terms: [BlockNumber; 3],
    /// Auction status.
    status: Status,
    /// Candle auction can have no winner.
    /// If auction is finalized, that means that the winner is determined.
    finalized: bool,
    /// Just a vector for the UI tests.
    vector: Vec<u8>,
}

impl Default for Auction {
    fn default() -> Auction {
        Auction {
            name: String::default(),
            subject: Hash::default(),
            bids: Bids::default(),
            terms: <[BlockNumber; 3]>::default(),
            status: Status::OpeningPeriod,
            finalized: false,
            vector: <Vec<u8>>::default(),
        }
    }
}

/// Way to fail a contract execution.
#[derive(Debug, Eq, PartialEq)]
pub enum Failure {
    Revert(String),
    Panic,
}

/// Event emitted when an auction being echoed.
pub struct AuctionEchoed {
    auction: Auction,
}

enum Event {
    AuctionEchoed(AuctionEchoed),
}

/// Storage of the contract.
#[derive(Default)]
pub struct Mother {
    auction: Auction,
    balances: Mapping<AccountId, Balance>,
}

impl Mother {
    fn init_env() -> Env {
        unimplemented!()
    }

    fn env(&self) -> Env {
        Self::init_env()
    }

    pub fn new(auction: Auction) -> Self {
        Self {
            balances: Default::default(),
            auction,
        }
    }

    pub fn new_default() -> Self {
        Default::default()
    }

    /// Demonstrates the ability to fail a constructor safely.
    pub fn failed_new(fail: bool) -> Result<Self, Failure> {
        if fail {
            Err(Failure::Revert("Reverting instantiation".to_string()))
        } else {
            Ok(Default::default())
        }
    }

    /// Takes an auction data struct as input and returns it back.
    pub fn echo_auction(&mut self, auction: Auction) -> Auction {
        self.env().emit_event(Event::AuctionEchoed(AuctionEchoed {
            auction: auction.clone(),
        }));
        auction
    }

    /// Fails contract execution in the required way.
    pub fn revert_or_trap(&mut self, fail: Option<Failure>) -> Result<(), Failure> {
        match fail {
            Some(Failure::Revert(_)) => {
                Err(Failure::Revert("Reverting on user demand!".to_string()))
            }
            Some(Failure::Panic) => {
                panic!("Trapping on user demand!")
            }
            None => Ok(()),
        }
    }

    /// Prints the specified string into node's debug log.
    pub fn debug_log(&mut self, _message: String) {
        println!("debug_log: {}", _message);
    }
}
