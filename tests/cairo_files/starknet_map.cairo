%lang starknet
%builtins pedersen range_check

from starkware.cairo.common.cairo_builtins import HashBuiltin

@storage_var
func my_storage_var(param1 : felt, param2 : felt) -> (res : felt):
end

@view
func get_my_storage_var{
        syscall_ptr : felt*,
        pedersen_ptr : HashBuiltin*,
        range_check_ptr
    }(param1 : felt, param2 : felt, value : felt) -> (
        value : felt
    ):
    let (res) = my_storage_var.read(param1, param2)
    return (res)
end

@external
func increase_my_storage_var{
        syscall_ptr : felt*,
        pedersen_ptr : HashBuiltin*,
        range_check_ptr
    }(param1 : felt, param2 : felt, value : felt):
    my_storage_var.write(param1, param2, value)
    return ()
end
