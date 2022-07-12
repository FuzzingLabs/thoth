%builtins output

from starkware.cairo.common.serialize import serialize_word

func main{output_ptr : felt*}():
    let a = 1234

    serialize_word(a)

    return ()
end