%builtins output

func test_symbolic_execution(f: felt, u: felt, z: felt, z2: felt, i: felt, n: felt, g: felt, l: felt, a: felt, b: felt, s: felt) {
    if (f == 'f') {    
        if (u == 'u') {
            if (z == 'z') {
                if (z2 == 'z') {
                    if (i == 'i') {
                        if (n == 'n') {
                            if (g == 'g') {
                                if (l == 'l') {
                                    if (a == 'a') {
                                        if (b == 'b') {
                                            if (s == 's') {
                                                return();
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    return();
}

func main{output_ptr: felt*}() {
    return ();
}