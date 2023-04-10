fn main() {
    let a = 1234_u128;
    let b = 5678_u128;

    let c0 = a & b; // libfunc output[1] -> AND
    let c1 = a ^ b; // libfunc output[2] -> XOR
    let c2 = a | b; // libfunc output[3] -> OR

    let c = c0 + c1 + c2;
}
