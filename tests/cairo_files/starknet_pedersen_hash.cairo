%lang starknet
%builtins pedersen range_check

from starkware.cairo.common.cairo_builtins import HashBuiltin
from starkware.cairo.common.hash import hash2

@view
func get_hash{pedersen_ptr: HashBuiltin*}(x, y) -> (
        hash: felt , hash_with_zero: felt):

    let (hash) = hash2{hash_ptr=pedersen_ptr}(x, y)

    let (hash_with_zero) = hash2{hash_ptr=pedersen_ptr}(x, 0)

    return (hash, hash_with_zero)
end