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

# Returns a list of VoteInfo instances representing the claimed
# votes.
# The validity of the returned data is not guaranteed and must
# be verified by the caller.
func get_claimed_votes() -> (votes : VoteInfo*, n : felt):
    alloc_locals
    local n
    let (votes : VoteInfo*) = alloc()
    %{
        #  We look inside the JSON input given by user
        #  and we count the number of element inside 'votes'
        ids.n = len(program_input['votes'])

        #  We take all the public keys inside the given JSON
        public_keys = [
            #  The 2 following lines work together
            #  they convert string with explicit base (here hexa:16)
            int(pub_key, 16)
            for pub_key in program_input['public_keys']]

        for i, vote in enumerate(program_input['votes']):
            # Get the address of the i-th vote.
            base_addr = \
                ids.votes.address_ + ids.VoteInfo.SIZE * i
            memory[base_addr + ids.VoteInfo.voter_id] = \
                vote['voter_id']
            memory[base_addr + ids.VoteInfo.pub_key] = \
                public_keys[vote['voter_id']]
            memory[base_addr + ids.VoteInfo.vote] = \
                vote['vote']
            memory[base_addr + ids.VoteInfo.r] = \
                int(vote['r'], 16)
            memory[base_addr + ids.VoteInfo.s] = \
                int(vote['s'], 16)
    %}
    return (votes=votes, n=n)
end

# The identifier that represents what we're voting for.
# This will appear in the user's signature to distinguish
# between different polls.
const POLL_ID = 10018

#  The name of this function make it transparent
func verify_vote_signature{pedersen_ptr : HashBuiltin*, ecdsa_ptr : SignatureBuiltin*}(
    vote_info_ptr : VoteInfo*
):
    let (message) = hash2{hash_ptr=pedersen_ptr}(x=POLL_ID, y=vote_info_ptr.vote)

    verify_ecdsa_signature(
        message=message,
        public_key=vote_info_ptr.pub_key,
        signature_r=vote_info_ptr.r,
        signature_s=vote_info_ptr.s,
    )
    return ()
end

#  The maximal number of voters to 2^10 = 1024
const LOG_N_VOTERS = 10

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

func init_voting_state() -> (state : VotingState):
    alloc_locals
    local state : VotingState

    #  We initialize the number of "yes" and "no" votes count of the state to 0
    assert state.n_yes_votes = 0
    assert state.n_no_votes = 0

    %{
        #  We take all the public keys inside the given JSON
        public_keys = [
            #  The 2 following lines work together
            #  they convert string with explicit base (here hexa:16)
            int(pub_key, 16)
            for pub_key in program_input['public_keys']]
        initial_dict = dict(enumerate(public_keys))
    %}

    #  dict_new() need implicit argument named initial_dict
    let (dict : DictAccess*) = dict_new()

    #  We initialize the start and end public key trees of the state to the dict values
    assert state.public_key_tree_start = dict
    assert state.public_key_tree_end = dict

    #  And we return the state
    return (state=state)
end

func process_vote{pedersen_ptr : HashBuiltin*, ecdsa_ptr : SignatureBuiltin*, state : VotingState}(
    vote_info_ptr : VoteInfo*
):
    alloc_locals

    # Verify that pub_key != 0.
    assert_not_zero(vote_info_ptr.pub_key)

    # Verify the signature's validity.
    verify_vote_signature(vote_info_ptr=vote_info_ptr)

    # Update the public key dict.
    let public_key_tree_end = state.public_key_tree_end
    #  dict_update comes from the imports, it need 3 things
    #  1: key, 2: previous value, 3: new value
    #  we override the implicit dict_ptr with our dict
    #  it's for we don't have to create a variable named dict_ptr and give our dict
    dict_update{dict_ptr=public_key_tree_end}(
        key=vote_info_ptr.voter_id, prev_value=vote_info_ptr.pub_key, new_value=0
    )

    # Generate the new state.
    local new_state : VotingState
    #  We initialize the new state with the 2 trees dict
    #  We aren't testing the values
    assert new_state.public_key_tree_start = (
        state.public_key_tree_start)
    assert new_state.public_key_tree_end = (
        public_key_tree_end)

    # Update the counters.
    tempvar vote = vote_info_ptr.vote
    if vote == 0:
        # Vote "No".
        assert new_state.n_yes_votes = state.n_yes_votes
        assert new_state.n_no_votes = state.n_no_votes + 1
    else:
        # Make sure that in this case vote=1.
        assert vote = 1

        # Vote "Yes".
        assert new_state.n_yes_votes = state.n_yes_votes + 1
        assert new_state.n_no_votes = state.n_no_votes
    end

    # Update the state.
    let state = new_state
    return ()
end

func process_votes{pedersen_ptr : HashBuiltin*, ecdsa_ptr : SignatureBuiltin*, state : VotingState}(
    votes : VoteInfo*, n_votes : felt
):
    if n_votes == 0:
        return ()
    end

    process_vote(vote_info_ptr=votes)

    process_votes(votes=votes + VoteInfo.SIZE, n_votes=n_votes - 1)
    return ()
end

struct BatchOutput:
    member n_yes_votes : felt
    member n_no_votes : felt
    member public_keys_root_before : felt
    member public_keys_root_after : felt
end

func main{
    output_ptr : felt*, pedersen_ptr : HashBuiltin*, range_check_ptr, ecdsa_ptr : SignatureBuiltin*
}():
    alloc_locals

    #  We convert the felt pointer to a pointer to BatchOutput
    #  so the type of the output reference is BatchOutput*
    let output = cast(output_ptr, BatchOutput*)
    let output_ptr = output_ptr + BatchOutput.SIZE

    #  We are looking for the votes inside the given JSON
    let (votes, n_votes) = get_claimed_votes()
    let (state) = init_voting_state()
    process_votes{state=state}(votes=votes, n_votes=n_votes)
    local pedersen_ptr : HashBuiltin* = pedersen_ptr
    local ecdsa_ptr : SignatureBuiltin* = ecdsa_ptr

    # Write the "yes" and "no" counts to the output.
    assert output.n_yes_votes = state.n_yes_votes
    assert output.n_no_votes = state.n_no_votes

    # Squash the dict.
    #  We are reducing the dict
    #  A squashed dictionary is one whose intermediate updates have been summarized
    #  and each key appears exactly once with its most recent value
    let (squashed_dict_start, squashed_dict_end) = dict_squash(
        dict_accesses_start=state.public_key_tree_start, dict_accesses_end=state.public_key_tree_end
    )
    local range_check_ptr = range_check_ptr

    # Compute the two Merkle roots.
    let (root_before, root_after) = small_merkle_tree_update{hash_ptr=pedersen_ptr}(
        squashed_dict_start=squashed_dict_start,
        squashed_dict_end=squashed_dict_end,
        height=LOG_N_VOTERS,
    )

    # Write the Merkle roots to the output.
    assert output.public_keys_root_before = root_before
    assert output.public_keys_root_after = root_after

    return ()
end