%lang starknet

from starkware.cairo.common.cairo_builtins import HashBuiltin

# Define a storage variable for the owner address.
@storage_var
func owner() -> (owner_address : felt):
end


# In a similar way to __default__, the __l1_default__ entry point is executed when an L1 handler is invoked but the requested selector is missing.
# This entry point in combination with the delegate_l1_handler system call can be used to forward L1 handlers.

@constructor
func constructor{
    syscall_ptr : felt*,
    pedersen_ptr : HashBuiltin*,
    range_check_ptr,
}(owner_address : felt):
    owner.write(value=owner_address)
    return ()
end