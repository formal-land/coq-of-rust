use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

#[derive(Hash)]
struct Person {
    id: u32,
    name: String,
    phone: u64,
}

fn calculate_hash<T: Hash>(t: &T) -> u64 {
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    s.finish()
}

fn main() {
    let person1 = Person {
        id: 5,
        name: "Janet".to_string(),
        phone: 555_666_7777,
    };
    let person2 = Person {
        id: 5,
        name: "Bob".to_string(),
        phone: 555_666_7777,
    };

    assert!(calculate_hash(&person1) != calculate_hash(&person2));
}
