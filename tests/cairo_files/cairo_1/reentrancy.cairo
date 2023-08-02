#[abi]
trait IAnotherContract {
    fn foo(a: felt252);
}

#[contract]
mod TestContract {
    use super::IAnotherContractDispatcherTrait;
    use super::IAnotherContractDispatcher;
    use starknet::ContractAddress;

    struct Storage {
        a: felt252,
        b: felt252,
    }

    #[external]
    fn good1(address: ContractAddress) {
        let a = a::read();
        a::write(4);
        IAnotherContractDispatcher { contract_address: address }.foo(a);
    }

    #[external]
    fn bad1(address: ContractAddress) {
        let a = a::read();
        IAnotherContractDispatcher { contract_address: address }.foo(a);
        a::write(4);
    }
    
    #[external]
    fn bad2(address: ContractAddress) {
        if 2 == 2 {
            let a = a::read();
            IAnotherContractDispatcher { contract_address: address }.foo(a);
        } else {
            let b = b::read();
            IAnotherContractDispatcher { contract_address: address }.foo(b);
        }
        a::write(4);
        b::write(4);
    }

    #[external]
    fn bad3(address: ContractAddress) {
        let a = a::read();
        internal_ext_call(address);
        a::write(4);
    }

    fn internal_ext_call(address: ContractAddress) {
        IAnotherContractDispatcher { contract_address: address }.foo(4);
    }

    #[external]
    fn bad4(address: ContractAddress) {
        internal_ext_call2(address);
        a::write(4);
    }

    fn internal_ext_call2(address: ContractAddress) {
        let a = a::read();
        IAnotherContractDispatcher { contract_address: address }.foo(4);
    }

}
