%lang starknet
%builtins pedersen range_check

from starkware.cairo.common.cairo_builtins import HashBuiltin

@storage_var
func my_tuple_storage_var() -> (res : (felt, felt, felt)):
end

@external
func modify_my_tuple_storage_var{
        syscall_ptr : felt*,
        pedersen_ptr : HashBuiltin*,
        range_check_ptr
    }(
        value_1 : felt,
        value_2 : felt,
        value_3 : felt
    ):
    
    my_tuple_storage_var.write((value_1, value_2, value_3))
    return ()
end
