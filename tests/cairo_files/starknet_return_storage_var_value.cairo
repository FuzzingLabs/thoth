%lang starknet
%builtins pedersen range_check

from starkware.cairo.common.cairo_builtins import HashBuiltin

@storage_var
func my_storage_var() -> (res : felt):
end

@view
func get_my_storage_var{
        syscall_ptr : felt*,
        pedersen_ptr : HashBuiltin*,
        range_check_ptr
    }() -> (
        value : felt
    ):
    let (value) = my_storage_var.read()
    return (value)
end