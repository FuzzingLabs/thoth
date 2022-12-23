%lang starknet
%builtins bitwise

from starkware.cairo.common.cairo_builtins import BitwiseBuiltin
from starkware.cairo.common.bitwise import (bitwise_operations,
bitwise_and, bitwise_xor, bitwise_or)

@view
func check_bitwise{bitwise_ptr: BitwiseBuiltin*}() -> ():

    let a = 1 * 2**3 + 1 * 2**2 + 0 * 2**1 + 0 * 2**0
    assert a = 1 * 8 + 1 * 4 + 0 * 2 + 0 * 1
    assert a = 12

    let b = 1 * 2**3 + 0 * 2**2 + 1 * 2**1 + 0 * 2**0
    assert b = 1 * 8 + 0 * 4 + 1 * 2 + 0 * 1
    assert b = 10

    let (a_and_b) = bitwise_and(a, b)
    assert a_and_b = 1 * 2**3 + 0 * 2**2 + 0 * 2**1 + 0 * 2**0

    let (a_xor_b) = bitwise_xor(a, b)
    assert a_xor_b = 0 * 2**3 + 1 * 2**2 + 1 * 2**1 + 0 * 2**0

    let (a_or_b) = bitwise_or(a, b)
    assert a_or_b = 1 * 2**3 + 1 * 2**2 + 1 * 2**1 + 0 * 2**0

    let (and, xor, or) = bitwise_operations(a, b)
    assert and = a_and_b
    assert xor = a_xor_b
    assert or = a_or_b

    let (c) = bitwise_or(2**250, 2**3)
    assert c = 2**250 + 2**3

    return ()
end