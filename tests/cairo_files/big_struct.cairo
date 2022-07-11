from starkware.cairo.common.dict import DictAccess

struct VotingState:
    # The number of "Yes" votes.
    member n_yes_votes : felt
    # The number of "No" votes.
    member n_no_votes : felt
    # Start and end pointers to a DictAccess array with the
    # changes to the public key Merkle tree.
    member public_key_tree_start : DictAccess*
    member public_key_tree_end : DictAccess*
end

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

struct BatchOutput:
    member n_yes_votes : felt
    member n_no_votes : felt
    member public_keys_root_before : felt
    member public_keys_root_after : felt
end

func main{}():
    ret
end