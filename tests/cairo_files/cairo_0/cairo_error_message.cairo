%builtins range_check

from starkware.cairo.common.math import assert_nn, assert_le

func main{range_check_ptr}():

    [ap] = -1; ap++

    with_attr error_message(
            "    ERROR: The given [ap-1] must be less than 60!"):
        assert_le([ap-1], -2)
    end


    [ap] = -1; ap++

    with_attr error_message(
            "    ERROR: The given [ap-1] must be positive!"):
        assert_nn([ap-1])
    end
    
    ret
end