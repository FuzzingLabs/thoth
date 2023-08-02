use option::OptionTrait;

#[contract]
mod UnusedReturn {
    struct Storage {
        value: felt252,
    }

    #[external]
    fn unused_return_1(amount: felt252) {
        f_1(amount);
    }

    #[external]
    fn unused_return_2(amount: felt252) {
        f_2(amount);
    }

    #[external]
    fn unused_return_3(amount: felt252) {
        f_3(amount);
    }

    #[external]
    fn unused_return_4(amount: felt252) {
        f_4(amount);
    }

    #[external]
    fn unused_return_5() {
        let a = f_5();        
    }

    #[external]
    fn no_report() {
        let a = value::read();
    }

    fn f_1(amount: felt252) -> felt252 {
        value::write(amount);
        23
    }

    fn f_2(amount: felt252) -> (felt252, felt252) {
        (amount, amount)
    }

    fn f_3(amount: felt252) -> felt252 {
        amount
    }

    fn f_4(amount: felt252) -> Option::<felt252> {
        Option::Some(amount)
    }

    fn f_5() -> felt252 {
        let a = value::read();
        a * 2
    }

}
