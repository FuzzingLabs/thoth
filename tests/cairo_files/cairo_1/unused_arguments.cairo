use array::ArrayTrait;

#[contract]
mod UnusedArguments { 
    struct Storage {
        value: felt252,
    }

    #[external]
    fn unused_1(a: felt252, b: felt252) {
        value::write(a);
    }

    #[external]
    fn unused_2(array: Array::<felt252>, l: felt252) -> felt252{
        1
    }

}
