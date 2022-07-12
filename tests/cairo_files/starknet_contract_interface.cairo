%lang starknet

from starkware.cairo.common.alloc import alloc
from starkware.cairo.common.cairo_builtins import HashBuiltin
from starkware.cairo.common.registers import get_fp_and_pc
from starkware.starknet.common.messages import send_message_to_l1
from starkware.starknet.common.syscalls import (
    get_caller_address,
    get_tx_info,
    storage_read,
    storage_write,
)

@contract_interface
namespace MyContract:
    func increase_value(address : felt, value : felt):
    end
end

@external
func increase_value{syscall_ptr : felt*}(address : felt, value : felt):
    let (res) = storage_read(address=address)
    return storage_write(address=address, value=res + value)
end