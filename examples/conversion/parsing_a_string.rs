fn main() {
    "12".parse::<i32>();
    "true".parse::<bool>();
    "unparsable".parse(); // we need the generics to know the type at compilation time
}
