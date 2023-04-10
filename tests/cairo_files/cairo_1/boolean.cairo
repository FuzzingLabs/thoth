fn main() -> felt252 {
    bool_to_felt252(((true | false) & !!false) ^ false)
}
