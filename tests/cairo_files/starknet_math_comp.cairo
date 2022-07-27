%lang starknet
%builtins pedersen range_check

from starkware.cairo.common.math_cmp import (
    is_not_zero, is_nn, is_le, is_nn_le, is_in_range,
    is_le_felt)

@view
func check_values{range_check_ptr}(
    number: felt) -> (
    a: felt, b: felt, c: felt, d: felt, e: felt, f: felt):

    alloc_locals
    let (local a) = is_not_zero(number)

    let (local b) = is_nn(number)

    let (local c) = is_le(number, 10)

    let (local d) = is_nn_le(number, 10)

    let (local e) = is_in_range(number, 10, 100)

    let g = 100
    let (local f) = is_le_felt(number, g)

    return (a, b, c, d, e, f)
end