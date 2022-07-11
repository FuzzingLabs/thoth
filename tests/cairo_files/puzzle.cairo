%builtins output range_check

from starkware.cairo.common.alloc import alloc
from starkware.cairo.common.math import assert_nn_le
from starkware.cairo.common.squash_dict import squash_dict
from starkware.cairo.common.serialize import serialize_word
from starkware.cairo.common.dict_access import DictAccess




struct Location:
    member row : felt
    member col : felt
end

struct KeyValue:
    member key : felt
    member value : felt
end


func output_initial_values{output_ptr : felt*}(
    squashed_dict : DictAccess*, n
):
    if n == 0:
        return ()
    end

    serialize_word(squashed_dict.prev_value)

    # Call output_initial_values recursively.
    return output_initial_values(
        squashed_dict=squashed_dict + DictAccess.SIZE, n=n - 1
    )
end

func finalize_state(dict : DictAccess*, idx) -> (
    dict : DictAccess*
):
    if idx == 0:
        return (dict=dict)
    end

    assert dict.key = idx
    assert dict.prev_value = idx - 1
    assert dict.new_value = idx - 1

    # Call finalize_state recursively.
    return finalize_state(
        dict=dict + DictAccess.SIZE, idx=idx - 1
    )
end

func build_dict(
    loc_list : Location*,
    tile_list : felt*,
    n_steps,
    dict : DictAccess*,
) -> (dict : DictAccess*):
    if n_steps == 0:
        # When there are no more steps, just return the dict
        # pointer.
        return (dict=dict)
    end

    # Set the key to the current tile being moved.
    assert dict.key = [tile_list]

    # Its previous location should be where the empty tile is
    # going to be.
    let next_loc : Location* = loc_list + Location.SIZE
    assert dict.prev_value = 4 * next_loc.row + next_loc.col

    # Its next location should be where the empty tile is
    # now.
    assert dict.new_value = 4 * loc_list.row + loc_list.col

    # Call build_dict recursively.
    return build_dict(
        loc_list=next_loc,
        tile_list=tile_list + 1,
        n_steps=n_steps - 1,
        dict=dict + DictAccess.SIZE,
    )
end


func verify_valid_location(loc : Location*):
    # Check that row is in the range 0-3.
    tempvar row = loc.row
    assert row * (row - 1) * (row - 2) * (row - 3) = 0

    # Check that col is in the range 0-3.
    tempvar col = loc.col
    assert col * (col - 1) * (col - 2) * (col - 3) = 0

    return ()
end

func verify_adjacent_locations(
    loc0 : Location*, loc1 : Location*
):
    alloc_locals
    local row_diff = loc0.row - loc1.row
    local col_diff = loc0.col - loc1.col

    if row_diff == 0:
        # The row coordinate is the same. Make sure the difference
        # in col is 1 or -1.
        assert col_diff * col_diff = 1
        return ()
    else:
        # Verify the difference in row is 1 or -1.
        assert row_diff * row_diff = 1
        # Verify that the col coordinate is the same.
        assert col_diff = 0
        return ()
    end
end

func verify_location_list(loc_list : Location*, n_steps):
    # Always verify that the location is valid, even if
    # n_steps = 0 (remember that there is always one more
    # location than steps).
    verify_valid_location(loc=loc_list)

    if n_steps == 0:
        return ()
    end

    verify_adjacent_locations(
        loc0=loc_list, loc1=loc_list + Location.SIZE
    )

    # Call verify_location_list recursively.
    verify_location_list(
        loc_list=loc_list + Location.SIZE, n_steps=n_steps - 1
    )
    return ()
end

func check_solution{output_ptr : felt*, range_check_ptr}(
    loc_list : Location*, tile_list : felt*, n_steps
):
    alloc_locals

    # Start by verifying that loc_list is valid.
    verify_location_list(loc_list=loc_list, n_steps=n_steps)

    # Allocate memory for the dict and the squashed dict.
    let (local dict_start : DictAccess*) = alloc()
    let (local squashed_dict : DictAccess*) = alloc()

    let (dict_end) = build_dict(
        loc_list=loc_list,
        tile_list=tile_list,
        n_steps=n_steps,
        dict=dict_start,
    )

    let (dict_end) = finalize_state(dict=dict_end, idx=15)

    let (squashed_dict_end : DictAccess*) = squash_dict(
        dict_accesses=dict_start,
        dict_accesses_end=dict_end,
        squashed_dict=squashed_dict,
    )

    # Store range_check_ptr in a local variable to make it
    # accessible after the call to output_initial_values().
    local range_check_ptr = range_check_ptr

    # Verify that the squashed dict has exactly 15 entries.
    # This will guarantee that all the values in the tile list
    # are in the range 1-15.
    assert squashed_dict_end - squashed_dict = 15 *
        DictAccess.SIZE

    output_initial_values(squashed_dict=squashed_dict, n=15)

    # Output the initial location of the empty tile.
    serialize_word(4 * loc_list.row + loc_list.col)

    # Output the number of steps.
    serialize_word(n_steps)

    return ()
end

func main{output_ptr : felt*, range_check_ptr}():
    alloc_locals

    # Declare two variables that will point to the two lists and
    # another variable that will contain the number of steps.
    local loc_list : Location*
    local tile_list : felt*
    local n_steps

    %{
        # The verifier doesn't care where those lists are
        # allocated or what values they contain, so we use a hint
        # to populate them.
        locations = program_input['loc_list']
        tiles = program_input['tile_list']

        ids.loc_list = loc_list = segments.add()
        for i, val in enumerate(locations):
            memory[loc_list + i] = val

        ids.tile_list = tile_list = segments.add()
        for i, val in enumerate(tiles):
            memory[tile_list + i] = val

        ids.n_steps = len(tiles)

        # Sanity check (only the prover runs this check).
        assert len(locations) == 2 * (len(tiles) + 1)
    %}

    check_solution(loc_list=loc_list, tile_list=tile_list, n_steps=n_steps)
    return ()
end