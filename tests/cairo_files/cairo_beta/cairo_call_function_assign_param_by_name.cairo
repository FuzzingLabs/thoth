func a{}(arg : felt):
	[ap] = arg; ap++
	ret
end

func b{}(first_arg : felt, second_arg : felt):
	[ap] = first_arg + second_arg; ap++
	ret
end

func main{}():
    a(arg=1)
    b(first_arg=1, second_arg=2)

    return ()
end
