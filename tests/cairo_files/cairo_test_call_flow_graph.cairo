%builtins output


func a_func { } ( ) -> (x : felt):
	let zzz = 111111111111111111
	let x = 10
	return(x)
end

func b_func { } ( ) -> (x : felt):
	let zzz = 111111111111111111
	let x = 10
	[ap + 10] = [fp] + 42
	return(x)
end

func c_func { } ( ) -> (x : felt):
	let zzz = 111111111111111111
	let x = 10
	b_func()
	a_func()
	[fp - 3] = [ap + 7] * [ap + 8]
	[ap + 10] = [fp] + 42
    c_func()
	return(x)
end


func main{output_ptr : felt*}() -> ():
	[fp + 1] = 5
	a_func()
	let zz = 222222222222222222222222
	b_func()
	c_func()
	ret
end