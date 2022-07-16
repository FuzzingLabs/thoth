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
    # Short strings are ASCII encoded humbers.
    # They are identified by single quotation marks.
    # They are actually just numbers (felts), not true strings.
    # 'ab' = a:61 b:62 = 0x6162 = 24930
    let short_string = 'ab'
    # Adding to a string does not make sense.
    # 24930 + 1 = 24931 = 0x6163 = a:61 c:63 = 'ac'
    let mangled_string = short_string + 1

    # h 68 e 65 l 6c l 6c o 6f
    # 0x68656c6c6f = 448378203247
    let hello_string = 'hello'
    return (user_number, short_string, mangled_string, hello_string)
end