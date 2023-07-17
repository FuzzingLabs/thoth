#[contract]
mod DeadCode {
    
    #[external]
    fn use_event(amount: felt252) -> felt252{
        add_1(amount)
    }

    fn add_1(amount: felt252) -> felt252 {
        amount + 1
    }

    fn add_2(amount: felt252) -> felt252 {
        amount + 2
    }

}
