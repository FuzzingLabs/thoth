%lang starknet

from starkware.cairo.common.cairo_builtins import HashBuiltin

# Define a storage variable for the owner address.
@storage_var
func owner() -> (owner_address : felt):
end


# constructor is a decorator and a function that is guaranteed to run during the contract deployment.
# Here we need an owner_address that has to be provided during the deployment

@constructor
func constructor{
    syscall_ptr : felt*,
    pedersen_ptr : HashBuiltin*,
    range_check_ptr,
}(owner_address : felt):
    owner.write(value=owner_address)
    return ()
end