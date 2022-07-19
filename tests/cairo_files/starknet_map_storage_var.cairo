%lang starknet

from starkware.cairo.common.alloc import alloc
from starkware.cairo.common.cairo_builtins import HashBuiltin, SignatureBuiltin
from starkware.cairo.common.hash_state import (
    hash_finalize,
    hash_init,
    hash_update,
    hash_update_single,
)
from starkware.cairo.common.memcpy import memcpy
from starkware.cairo.common.registers import get_fp_and_pc
from starkware.cairo.common.signature import verify_ecdsa_signature
from starkware.starknet.common.syscalls import (
    call_contract,
    get_caller_address,
    get_contract_address,
    get_tx_info,
)

@storage_var
func my_storage_var(param1 : felt, param2 : felt) -> (res : felt):
end

@external
func record_inventory{syscall_ptr : felt*, pedersen_ptr : HashBuiltin*, range_check_ptr}(param1 : felt, param2 : felt, value : felt):
    my_storage_var.write(param1, param2, value)
    return ()
end

@view
func read_inventory{pedersen_ptr : HashBuiltin*, range_check_ptr}(param1 : felt, param2 : felt) -> (res : felt):
    alloc_locals
    let (local res) = my_storage_var.read(param1, param2)
    return (res)
end