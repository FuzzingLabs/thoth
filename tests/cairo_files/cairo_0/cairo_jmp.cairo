%builtins output

from starkware.cairo.common.serialize import serialize_word

func main{output_ptr : felt*}():
    jmp test

	[ap] = 1; ap++
	jmp rel 6

	test:
	[ap] = 2; ap++


    serialize_word([ap-1])
	return ()
end