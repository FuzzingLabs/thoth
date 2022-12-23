%lang starknet
%builtins pedersen range_check bitwise

from starkware.cairo.common.cairo_builtins import HashBuiltin
from starkware.starknet.common.syscalls import library_call

# The implementation class hash.
@storage_var
func implementation_hash() -> (class_hash : felt):
end

@constructor
func constructor{
    syscall_ptr : felt*,
    pedersen_ptr : HashBuiltin*,
    range_check_ptr,
}(implementation_hash_ : felt):
    implementation_hash.write(value=implementation_hash_)
    return ()
end

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
    let (class_hash) = implementation_hash.read()

    let (retdata_size : felt, retdata : felt*) = library_call(
        class_hash=class_hash,
        function_selector=selector,
        calldata_size=calldata_size,
        calldata=calldata,
    )
    return (retdata_size=retdata_size, retdata=retdata)
end