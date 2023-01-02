%builtins output

from starkware.cairo.common.serialize import serialize_word

struct MyClass:
        member a : felt
        member b : felt
end

func main{output_ptr : felt*}():
    alloc_locals

    local a : MyClass
    a.a = 1
    a.b = 2

    let b = &a

    serialize_word(b.b)

    return ()
end