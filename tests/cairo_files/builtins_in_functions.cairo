%builtins output pedersen range_check ecdsa

from starkware.cairo.common.cairo_builtins import HashBuiltin, SignatureBuiltin

func o{output_ptr : felt*}():
	ret
end

func p{pedersen_ptr : HashBuiltin*}():
	ret
end

func r{range_check_ptr}():
	ret
end

func e{ecdsa_ptr : SignatureBuiltin*}():
	ret
end

func empty{}():
	ret
end

func main{
    output_ptr : felt*, pedersen_ptr : HashBuiltin*, range_check_ptr, ecdsa_ptr : SignatureBuiltin*
}():
	o()
	p()
	r()
	e()
	empty()
	ret
end