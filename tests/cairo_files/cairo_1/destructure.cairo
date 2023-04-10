struct MyStruct {
    a: felt252,
    b: felt252,
    c: felt252,
}

fn main() {
    let MyStruct { a, b, .. } = MyStruct {
        a: 12,
        b: 34,
        c: 56,
    };
}
