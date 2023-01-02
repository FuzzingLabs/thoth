%builtins output

func test_symbolic_execution(x: felt, y: felt) {
    if (x == 10) {
        return();
    }
    
    if (x == 20) {
        return();
    }
    
    if (y == 15) {
        return();
    }
    
    if (y == 25) {
        return();
    }
    return();
}

func main{output_ptr: felt*}() {
    tempvar x = 10;
    tempvar y = 20;
    test_symbolic_execution(x, y);
    return ();
}