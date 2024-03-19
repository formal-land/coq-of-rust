struct Account {
    id: i32,
    balance: u32,
}

struct Bank {
    accounts: Vec<Account>,
}

impl Bank {
    fn transfer(&mut self, from: i32, to: i32, amount: u32) {
        let from_index = self.accounts.iter().position(|&x| x.id == from);
        let to_index = self.accounts.iter().position(|&x| x.id == to);
        if from_index.is_none() || to_index.is_none() {
            return;
        }
        let from_index = from_index.unwrap();
        let to_index = to_index.unwrap();
        if self.accounts[from_index].balance < amount {
            return;
        }
        self.accounts[from_index].balance -= amount;
        self.accounts[to_index].balance += amount;
    }
}
