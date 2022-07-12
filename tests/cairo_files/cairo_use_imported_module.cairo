%builtins range_check

from starkware.cairo.common.math import assert_nn, assert_le, assert_lt, assert_nn_le, assert_in_range, assert_250_bit

func main{range_check_ptr}():

	let a = 0
	let b = 1
	let c = 2

	assert_nn(b)
	assert_nn(c)

	assert_le(a, a)
	assert_le(a, b)
	assert_le(a, c)
	assert_le(b, b)
	assert_le(b, c)
	assert_le(c, c)

	assert_lt(a, b)
	assert_lt(b, c)

	assert_nn_le(b, c)
	assert_nn_le(b, b)
	assert_nn_le(c, c)

	# a <= a < b
	assert_in_range(a, a, b)
	# a <= a < c
	assert_in_range(a, a, c)
	# a <= b < c
	assert_in_range(b, a, c)
	# b <= b < c
	assert_in_range(b, b, c)

	assert_250_bit(a)
	assert_250_bit(b)
	assert_250_bit(c)
	ret
end
