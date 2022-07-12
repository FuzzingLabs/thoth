from starkware.cairo.common.alloc import alloc

struct aStruct:
    member a : felt
    member b : felt
    member c : felt
    member d : felt
end

struct aSecondStruct:
    member a : felt
    member b : felt
end

func main{}():
    alloc_locals

    # This line is not translated into a Cairo instruction
    # It is just used by the compiler to replace a_constant with 1234
    const a_constant = 1234

    # Local variables can be accessed from their definition up to the end of the function
    # If you use local variables, the first line of your function must be alloc_locals
    local a_local_variable = 1234

    # Temporary variables that can be used at most inside one operation
    tempvar a_temp_variable = 1234

    # Point is a new type, it's an alias to (x : felt, y : felt)
    using Point = (x : felt, y : felt)

    # 
    let a_variable = 1234

    let ptr : aStruct* = cast([fp], aStruct*)
    # this is equal to let ptr = cast([fp], aStruct*)
    assert ptr.a = 1
    assert ptr.b = 2
    assert ptr.c = 3
    assert ptr.d = 4

    # Tuple
    local pt : (x : felt, y : felt) = (x=2, y=3)

    # Here a = 2
    let a = (1, 2, 3, 4)[2]

    # Array
    let (struct_array : aSecondStruct*) = alloc()
    assert struct_array[0] = aSecondStruct(a=1, b=2)
    assert struct_array[1] = aSecondStruct(a=3, b=4)
    assert struct_array[2] = aSecondStruct(a=5, b=6)

    # new operator
    tempvar temp_var_for_new : aSecondStruct* = new aSecondStruct(a=1, b=2)

    # Array of struct
    tempvar arr : aSecondStruct* = cast(
        new (aSecondStruct(a=1, b=2), aSecondStruct(a=3, b=4)), aSecondStruct*)

    ret
end