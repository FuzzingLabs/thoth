%builtins output pedersen range_check ecdsa

from starkware.cairo.common.alloc import alloc
from starkware.cairo.common.cairo_builtins import HashBuiltin, SignatureBuiltin
from starkware.cairo.common.dict import DictAccess, dict_new, dict_squash, dict_update
from starkware.cairo.common.hash import hash2
from starkware.cairo.common.math import assert_not_zero
from starkware.cairo.common.signature import verify_ecdsa_signature
from starkware.cairo.common.small_merkle_tree import small_merkle_tree_update

struct VoteInfo:
    # The ID of the voter.
    member voter_id : felt
    # The voter's public key.
    member pub_key : felt
    # The vote (0 or 1).
    member vote : felt
    # The ECDSA signature (r and s).
    member r : felt
    member s : felt
end

func get_claimed_votes() -> (votes : VoteInfo*, n : felt):
    alloc_locals
    local n
    let (votes : VoteInfo*) = alloc()
    return (votes=votes, n=n)
end

func main{
    output_ptr : felt*, pedersen_ptr : HashBuiltin*, range_check_ptr, ecdsa_ptr : SignatureBuiltin*
}():

    return ()
end