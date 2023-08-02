#[abi]
trait IAnotherContract {
    fn foo(a: felt252);
}

#[contract]
mod TestContract {
    use super::IAnotherContractDispatcherTrait;
    use super::IAnotherContractDispatcher;
    use starknet::ContractAddress;

    #[event]
    fn MyEvent() {}

    struct Storage {}

    #[external]
    fn good1(address: ContractAddress) {
        MyEvent();
        IAnotherContractDispatcher { contract_address: address }.foo(4);
    }

    #[external]
    fn bad1(address: ContractAddress) {
        IAnotherContractDispatcher { contract_address: address }.foo(4);
        MyEvent();
    }

}
