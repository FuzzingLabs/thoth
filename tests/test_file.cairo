%builtins output


func a_func { } ( ) -> (x : felt):
	let zzz = 111111111111111111
	let x = 10
	return(x)
end


func main{output_ptr : felt*}() -> ():
	[fp + 1] = 5
	[ap + 2] = 42
	[ap] = [fp]; ap++
	[fp - 3] = [fp + 7]
	[ap - 3] = [ap]
	[fp + 1] = [ap] + [fp]
	[ap + 10] = [fp] + [fp - 1]
	[ap + 1] = [ap - 7] * [fp + 3]
	[ap + 10] = [fp] * [fp - 1]
	[fp - 3] = [ap + 7] * [ap + 8]
	[ap + 10] = [fp] + 42
	[fp + 1] = [[ap + 2] + 3]; ap++
	[ap + 2] = [[fp]]
	[ap + 2] = [[ap - 4] + 7]; ap++ 
	let z = 1
	let x = 100
	[ap] = 11; ap++
	let zz = 222222222222222222222222
	[ap] = 99999; ap++
	[ap] = [ap - 1] - x; ap++
	[ap] = [ap - 1] - x; ap++
	[ap] = [ap - 2] - x; ap++
	[ap] = [ap - 2] + [fp]; ap++
	[ap] = 1234567; ap++
	[ap] = [ap - 1] - 100; ap++
	[ap] = [ap - 1] * 100; ap++
	[ap] = [[ap-1]+3]
	[ap + 2] = [[fp]]
	[ap] = 1234567
	ret
end