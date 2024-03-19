fn get_at_index(vector: Vec<i32>, index: usize) -> Option<i32> {
    if index < vector.len() {
        return Some(vector[index]);
    }

    None
}

struct Bank {
    accounts: Vec<u32>,
}

impl Bank {
    fn transfer(&mut self, from: usize, to: usize, amount: u32) {
        if from >= self.accounts.len() || to >= self.accounts.len() {
            return;
        }

        if self.accounts[from] < amount {
            return;
        }

        self.accounts[from] -= amount;
        self.accounts[to] += amount;
    }
}
