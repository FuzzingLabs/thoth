%lang starknet

from starkware.cairo.common.registers import get_fp_and_pc

@view
func test_tuple_and_pointers(number : felt) -> (res : felt):
    let (tuple) = alloc_tuple_and_give_pointer(number)
    let val = tuple[2]
    return (val)
end


func alloc_tuple_and_give_pointer(val : felt) -> (a_tuple : felt*):
    alloc_locals
    local tuple : (felt, felt, felt) = (5, 6, 2*val)
    let (__fp__, _) = get_fp_and_pc()
    return (&tuple)
end
