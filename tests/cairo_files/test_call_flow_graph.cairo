%builtins output


func a_func { } ( ) -> (x : felt):
	let x = 10
	return(x)
end

func b_func { } ( ) -> (x : felt):
	let x = 50
    a_func()
	return(x)
end

func c_func { } ( ) -> (x : felt):
    a_func()
    b_func()
	ret
end