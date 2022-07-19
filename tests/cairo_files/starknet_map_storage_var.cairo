%lang starknet
%builtins pedersen range_check

from starkware.cairo.common.cairo_builtins import HashBuiltin
from starkware.starknet.common.storage import Storage


@storage_var
func my_storage_var(param1 : felt, param2 : felt) -> (res : felt):
end

@external
func record_inventory{storage_ptr : Storage*, pedersen_ptr : HashBuiltin*,range_check_ptr}(param1 : felt, param2 : felt, value : felt):
    my_storage_var.write(param1, param2, value)
    return ()
end

@view
func read_inventory{storage_ptr : Storage*, pedersen_ptr : HashBuiltin*, range_check_ptr}(param1 : felt, param2 : felt) -> (res : felt):
    alloc_locals
    let (local res) = my_storage_var.read(param1, param2)
    return (res)
end