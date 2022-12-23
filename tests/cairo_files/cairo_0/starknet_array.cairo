%lang starknet
%builtins range_check

from starkware.cairo.common.math import assert_in_range
from starkware.cairo.common.alloc import alloc

@view
func read_array{
        range_check_ptr
    }(
        index : felt
    ) -> (
        value : felt
    ):

    assert_in_range(index, 0, 4)

    let (felt_array : felt*) = alloc()

    assert [felt_array] = 0
    assert [felt_array + 1] = 1
    assert [felt_array + 2] = 2 
    assert [felt_array + 3] = 3

    let val = felt_array[index]
    return (val)
end
