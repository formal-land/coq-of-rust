pub(crate) struct LoopA {}

impl LoopA {
    pub(crate) fn new() -> Self {
        LoopA {}
    }

    pub(crate) fn start_loop(&self) -> LoopB {
        LoopB::start_loop()
    }
}

pub(crate) enum LoopB {
    Item {
        #[allow(dead_code)]
        ident: LoopA,
    },
}

impl LoopB {
    pub(crate) fn start_loop() -> Self {
        LoopB::Item {
            ident: LoopA::new(),
        }
    }
}

#[allow(unused_variables)]
pub fn start_loop() {
    // The following code would bypass the compiler and crash the `rustc` thread
    let la = LoopA::new();
    let lb = la.start_loop();
}