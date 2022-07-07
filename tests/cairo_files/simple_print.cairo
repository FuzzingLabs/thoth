%builtins output

from starkware.cairo.common.serialize import serialize_word

func main{output_ptr : felt*}():

    let x = 100

    let y = x/2

    serialize_word(y)
    
    ret
end