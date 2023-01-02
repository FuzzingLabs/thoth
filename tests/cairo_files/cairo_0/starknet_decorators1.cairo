# Declare this file as a StarkNet contract.
%lang starknet

from starkware.cairo.common.cairo_builtins import HashBuiltin

# Define a storage variable.
@storage_var
func balance() -> (res : felt):
end

# This decorator is used to create external functions, which may be called by the users of StarkNet, and by other contracts.
# Increases the balance by the given amount.
@external
func increase_balance{
    syscall_ptr : felt*,
    pedersen_ptr : HashBuiltin*,
    range_check_ptr,
}(amount : felt):
    let (res) = balance.read()
    balance.write(res + amount)
    return ()
end

# The @view decorator is identical to the @external decorator.
# The only difference is that the method is annotated as a method that only queries the state rather than modifying it.
# Returns the current balance.
@view
func get_balance{
    syscall_ptr : felt*,
    pedersen_ptr : HashBuiltin*,
    range_check_ptr,
}() -> (res : felt):
    let (res) = balance.read()
    return (res)
end