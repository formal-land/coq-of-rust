fn id(x: u64) -> u64 {
    x
}

fn tri(a: u64, b: u64, c: u64) {}

fn main() {
    id(0);
    id(id(0));
    id(id(id(0)));
    // id(id(id(id(0))));
    // tri(id(1), id(2), 3);
}
