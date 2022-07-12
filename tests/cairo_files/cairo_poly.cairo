%builtins output

from starkware.cairo.common.serialize import serialize_word

func main{output_ptr : felt*}():

    let x = 100
    
    [ap] = x; ap++

    [ap] = [ap - 1] * [ap - 1]; ap++

    [ap] = [ap - 1] * [ap - 2]; ap++

    [ap] = [ap - 2] * 23; ap++

    [ap] = [ap - 4] * 45; ap++

    [ap] = [ap - 3] + [ap - 2]; ap++

    [ap] = [ap - 1] + [ap - 2]; ap++

    [ap] = [ap - 1] + 67; ap++

    serialize_word([ap - 1])
    
    ret
end
