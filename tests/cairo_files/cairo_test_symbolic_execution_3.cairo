%builtins output

func test_symbolic_execution(f: felt, u: felt, z: felt, z2: felt, i: felt, n: felt, g: felt, l: felt, a: felt, b: felt, s: felt) {
    if (f == 6) {    
        if (u == 21) {
            if (z == 26) {
                if (z2 == 26) {
                    if (i == 9) {
                        if (n == 14) {
                            if (g == 7) {
                                if (l == 12) {
                                    if (a == 1) {
                                        if (b == 2) {
                                            if (s == 19) {
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