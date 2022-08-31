%lang starknet
%builtins range_check

@view
func echo_world(
        user_number : felt
    ) -> (
        user_number_echoed : felt,
        short_string : felt,
        mangled_string : felt,
        hello_string : felt,
    ):
    let short_string = 'ab'
    let mangled_string = short_string + 1
    let hello_string = 'hello'
    return (user_number, short_string, mangled_string, hello_string)
end
