#[derive(Default, Clone, Copy)]
struct AccountId(u128);

type Balance = u128;

type BlockNumber = u32;

struct Env {
    caller: AccountId,
}

pub trait Flip {
    /// Flips the current value of the Flipper's boolean.
    fn flip(&mut self);

    /// Returns the current value of the Flipper's boolean.
    fn get(&self) -> bool;

    fn push_foo(&mut self, value: bool);
}

/// Feature gated event
pub struct Changes {
    // attributing event field with `cfg` is not allowed
    new_value: bool,
    by: AccountId,
}

/// Feature gated event
pub struct ChangesDated {
    // attributing event field with `cfg` is not allowed
    new_value: bool,
    by: AccountId,
    when: BlockNumber,
}

enum Event {
    Changes(Changes),
    ChangesDated(ChangesDated),
}

impl Env {
    fn caller(&self) -> AccountId {
        self.caller
    }

    fn emit_event(&self, _event: Event) {
        unimplemented!()
    }

    fn block_number(&self) -> BlockNumber {
        unimplemented!()
    }
}

pub struct ConditionalCompilation {
    value: bool,
}

impl ConditionalCompilation {
    fn init_env() -> Env {
        unimplemented!()
    }

    fn env(&self) -> Env {
        Self::init_env()
    }

    /// Creates a new flipper smart contract initialized to `false`.
    pub fn new() -> Self {
        Self {
            value: Default::default(),
        }
    }

    /// Constructor that is included when `foo` is enabled
    pub fn new_foo(value: bool) -> Self {
        Self { value }
    }

    /// Constructor that is included when `bar` is enabled
    pub fn new_bar(value: bool) -> Self {
        Self { value }
    }

    /// Constructor that is included with either `foo` or `bar` features enabled
    pub fn new_foo_bar(value: bool) -> Self {
        Self { value }
    }

    pub fn inherent_flip_foo(&mut self) {
        self.value = !self.value;
        let caller = Self::init_env().caller();
        Self::init_env().emit_event(Event::Changes(Changes {
            new_value: self.value,
            by: caller,
        }));
    }

    pub fn inherent_flip_bar(&mut self) {
        let caller = Self::init_env().caller();
        let block_number = Self::init_env().block_number();
        self.value = !self.value;
        Self::init_env().emit_event(Event::ChangesDated(ChangesDated {
            new_value: self.value,
            by: caller,
            when: block_number,
        }));
    }
}

impl Flip for ConditionalCompilation {
    fn flip(&mut self) {
        self.value = !self.value;
    }

    fn get(&self) -> bool {
        self.value
    }

    /// Feature gated mutating message
    fn push_foo(&mut self, value: bool) {
        let caller = Self::init_env().caller();
        Self::init_env().emit_event(Event::Changes(Changes {
            new_value: value,
            by: caller,
        }));
        self.value = value;
    }
}
