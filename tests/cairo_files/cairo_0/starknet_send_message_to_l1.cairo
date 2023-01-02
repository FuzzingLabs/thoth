%lang starknet
%builtins pedersen range_check

from starkware.cairo.common.alloc import alloc
from starkware.starknet.common.messages import send_message_to_l1

# Generates a message that an L1 contract can use.
@external
func generate{
        syscall_ptr : felt*, range_check_ptr}():
    # Messages use the pointer 'syscall_ptr'.

    # A message is sent as a pointer to a list.
    let (message : felt*) = alloc()
    assert message[0] = 444
    assert message[1] = 333

    # Send the message with the three required arguments.
    send_message_to_l1(
        to_address=0x123123,
        payload_size=2,
        payload=message)
    return ()
end