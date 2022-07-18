%lang starknet
%builtins range_check

from starkware.cairo.common.cairo_builtins import HashBuiltin
from tests.cairo_files.starknet_math_utils_for_other_contract import add_two, get_modulo

@view
func get_calculations{
        range_check_ptr
    }(
        first : felt,
        second : felt
    ) -> (
        sum : felt,
        modulo : felt
    ):
    let (sum) = add_two(first, second)
    let (modulo) = get_modulo(first, second)
    return (sum, modulo)
end
