from starkware.cairo.common.dict import DictAccess

struct VotingState:
    member n_yes_votes : felt
    member n_no_votes : felt
    member public_key_tree_start : DictAccess*
    member public_key_tree_end : DictAccess*
end

struct VoteInfo:
    member voter_id : felt
    member pub_key : felt
    member vote : felt
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