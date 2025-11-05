#[derive(Clone, Debug, Default)]
pub struct CycleTracker {
    /// Stack of span names, with most recent at the end
    stack: Vec<String>,
}

impl CycleTracker {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn top(&self) -> Option<&String> {
        self.stack.last()
    }

    /// Starts a new cycle tracker span for the given name.
    /// If a span already exists for the given name, it ends the existing span and pushes a new one
    /// to the vec.
    pub fn start(&mut self, mut name: String) {
        // hack to remove "CT-" prefix
        if name.starts_with("CT-") {
            name = name.split_off(3);
        }
        self.stack.push(name);
    }

    /// Ends the cycle tracker span for the given name.
    /// If no span exists for the given name, it panics.
    pub fn end(&mut self, mut name: String) {
        // hack to remove "CT-" prefix
        if name.starts_with("CT-") {
            name = name.split_off(3);
        }
        let stack_top = self.stack.pop();
        assert_eq!(stack_top.unwrap(), name, "Stack top does not match name");
    }

    /// Ends the current cycle tracker span.
    pub fn force_end(&mut self) {
        self.stack.pop();
    }

    /// Get full name of span with all parent names separated by ";" in flamegraph format
    pub fn get_full_name(&self) -> String {
        self.stack.join(";")
    }
}

#[cfg(feature = "bench-metrics")]
mod emit {
    use metrics::counter;

    use super::CycleTracker;

    impl CycleTracker {
        pub fn increment_opcode(&self, (dsl_ir, opcode): &(Option<String>, String)) {
            let labels = [
                ("opcode", opcode.clone()),
                ("dsl_ir", dsl_ir.clone().unwrap_or_default()),
                ("cycle_tracker_span", self.get_full_name()),
            ];
            counter!("frequency", &labels).increment(1u64);
        }

        pub fn increment_cells_used(
            &self,
            (dsl_ir, opcode, air_name): &(Option<String>, String, String),
            trace_cells_used: usize,
        ) {
            if trace_cells_used == 0 {
                return;
            }
            let labels = [
                ("air_name", air_name.clone()),
                ("opcode", opcode.clone()),
                ("dsl_ir", dsl_ir.clone().unwrap_or_default()),
                ("cycle_tracker_span", self.get_full_name()),
            ];
            counter!("cells_used", &labels).increment(trace_cells_used as u64);
        }
    }
}
