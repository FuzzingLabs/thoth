%builtins output

func sum2(x: felt, y: felt) -> felt {
    return (x+y);
}

func main{output_ptr: felt*}() {
    tempvar x;
    tempvar y;
    if (sum2(x, y) == 10) {
        return ();
    }
    return ();
}