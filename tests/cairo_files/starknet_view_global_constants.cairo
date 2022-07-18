%lang starknet
%builtins range_check

const const_1 = 123456
const const_2 = 123456789

@view
func get_constants() -> (number_1 : felt, number_2 : felt):
    return (const_1, const_2)
end
