%lang starknet
%builtins pedersen range_check

from starkware.cairo.common.cairo_builtins import HashBuiltin

@storage_var
func my_tuple_storage_var() -> (res : (felt, felt, felt)):
end

@view
func get_my_tuple_storage_var{
        syscall_ptr : felt*,
        pedersen_ptr : HashBuiltin*,
        range_check_ptr
    }() -> (
        value_1 : felt,
        value_2 : felt,
        value_3 : felt
    ):
    let (the_tuple) = my_tuple_storage_var.read()
    let value_1 = the_tuple[0]
    let value_2 = the_tuple[1]
    let value_3 = the_tuple[2]
    return (value_1=value_1, value_2=value_2, value_3=value_3)
end
