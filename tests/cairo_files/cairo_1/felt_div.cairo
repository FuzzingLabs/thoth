use debug::PrintTrait;

fn main() {
    let x = 5;
    let y = 3;

    let z = felt252_div(x, felt_to_nonzero(y));

    // Should print 2412335192444087475798215188730046737082071476887731133315394704090581346989.
    z.print();
}

fn felt_to_nonzero(value: felt252) -> NonZero<felt252> {
    match felt252_is_zero(value) {
        IsZeroResult::Zero(()) => panic(ArrayTrait::new()),
        IsZeroResult::NonZero(x) => x,
    }
}
