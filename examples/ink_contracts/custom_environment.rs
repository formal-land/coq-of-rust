#[derive(Default, Clone, Copy)]
struct AccountId(u128);

type Balance = u128;

struct Env {
    caller: AccountId,
}

/// Trivial contract with a single message that emits an event with many topics.
#[derive(Default)]
pub struct Topics;

/// An event that would be forbidden in the default environment, but is completely
/// valid in our custom one.
#[derive(Default)]
pub struct EventWithTopics {
    first_topic: Balance,
    second_topic: Balance,
    third_topic: Balance,
    fourth_topic: Balance,
    fifth_topic: Balance,
}

enum Event {
    EventWithTopics(EventWithTopics),
}

impl Env {
    fn caller(&self) -> AccountId {
        self.caller
    }

    fn emit_event(&self, _event: Event) {
        unimplemented!()
    }
}

impl Topics {
    fn init_env() -> Env {
        unimplemented!()
    }

    fn env(&self) -> Env {
        Self::init_env()
    }

    pub fn new() -> Self {
        Default::default()
    }

    /// Emit an event with many topics.
    pub fn trigger(&mut self) {
        self.env()
            .emit_event(Event::EventWithTopics(EventWithTopics::default()));
    }
}
