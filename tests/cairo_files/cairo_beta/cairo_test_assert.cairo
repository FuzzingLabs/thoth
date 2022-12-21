%builtins output

from starkware.cairo.common.serialize import serialize_word

func main{output_ptr : felt*}():
	
	[ap] = 1
	assert [ap] = 5 

    serialize_word([ap])

    ret
end
