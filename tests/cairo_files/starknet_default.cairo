%lang starknet
%builtins pedersen range_check bitwise

from starkware.cairo.common.cairo_builtins import HashBuiltin
from starkware.starknet.common.syscalls import delegate_call

# The address of the implementation contract.
@storage_var
func impl_address() -> (address : felt):
end

@external
func constructor{
    syscall_ptr : felt*,
    pedersen_ptr : HashBuiltin*,
    range_check_ptr,
}(impl_address_ : felt):
    impl_address.write(value=impl_address_)
    return ()
end


# The __default__ entry point is executed if the requested selector does not match any of the entry point selectors in the contract.

# @raw_input : It instructs the compiler to pass the calldata as-is to the entry point, instead of parsing it into the requested arguments.
# If we use @raw_input we need those arguments: selector, calldata_size and calldata.

# @raw_output : It instructs the compiler not to process the function’s return value.
# If we use @raw_output the function’s return values must be retdata_size and retdata.

@external
@raw_input
@raw_output
func __default__{
    syscall_ptr : felt*,
    pedersen_ptr : HashBuiltin*,
    range_check_ptr,
}(selector : felt, calldata_size : felt, calldata : felt*) -> (
    retdata_size : felt, retdata : felt*
):
    let (address) = impl_address.read()

    let (retdata_size : felt, retdata : felt*) = delegate_call(
        contract_address=address,
        function_selector=selector,
        calldata_size=calldata_size,
        calldata=calldata,
    )
    return (retdata_size=retdata_size, retdata=retdata)
end