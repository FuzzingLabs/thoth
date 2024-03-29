%lang starknet
%builtins pedersen range_check

from starkware.cairo.common.cairo_builtins import HashBuiltin

@storage_var
func message_sum_storage_var() -> (res : felt):
end

@l1_handler
func receive{
    syscall_ptr : felt*,
    pedersen_ptr : HashBuiltin*,
    range_check_ptr,
}(from_address : felt,
        message_index_0 : felt, message_index_1 : felt):

    tempvar messages_sum = message_index_0 + message_index_1
    message_sum_storage_var.write(messages_sum)

    return ()
end