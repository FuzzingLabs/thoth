%lang starknet

from starkware.cairo.common.math import unsigned_div_rem

func add_two(
        a : felt,
        b : felt
    ) -> (
        sum : felt
    ):
    let sum = a + b
    return (sum)
end

func get_modulo{
        range_check_ptr
    }(
        a : felt,
        b : felt
    ) -> (
        result : felt
    ):
    let (dividend, remainder) = unsigned_div_rem(a, b)
    return (remainder)
end