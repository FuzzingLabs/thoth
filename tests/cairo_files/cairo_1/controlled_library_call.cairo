#[abi]
trait IAnotherContract {
    fn foo(a: u128) -> u128;
}

#[contract]
mod TestContract {
    use super::IAnotherContractDispatcherTrait;
    use super::IAnotherContractLibraryDispatcher;
    use starknet::class_hash::ClassHash;

    #[external]
    fn bad1(class_hash: ClassHash) -> u128 {
        IAnotherContractLibraryDispatcher { class_hash: class_hash }.foo(2_u128)
    }

    #[external]
    fn bad2(class_hash: ClassHash) -> u128 {
        internal_lib_call(class_hash)
    }

    fn internal_lib_call(class_hash: ClassHash) -> u128 {
        IAnotherContractLibraryDispatcher { class_hash: class_hash }.foo(2_u128)
    }

    #[external]
    fn good() -> u128 {
        IAnotherContractLibraryDispatcher { class_hash: starknet::class_hash_const::<0>() }.foo(2_u128)
    }

}
