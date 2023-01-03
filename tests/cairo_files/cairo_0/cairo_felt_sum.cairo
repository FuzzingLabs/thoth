%builtins output

func sum2(x: felt, y: felt) -> felt {
    return x + y;
}

func main{output_ptr: felt*}() {
    let x = 1;
    let y = 2;
    let sum = sum2(x, y); 
    return ();
}