fn factorial(n: felt) -> felt{
    if (n == 1) {
        return 1;
    } 

    let result = n * factorial(n - 1);
    return result;
}

fn recursion_test() {
    let n = 5;
    let factorial = factorial(n); 
}