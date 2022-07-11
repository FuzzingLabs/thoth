%builtins output

from starkware.cairo.common.serialize import serialize_word

func a{}() -> (b : felt):
    return (5)
end

func main{output_ptr : felt*}():
    a()
    if [ap-1] == 5:
        serialize_word(5)
        return ()
    else:
        serialize_word(10)
    end
    return ()
end