fn fib(a: felt252, b: felt252, n: felt252) -> felt252 {
    match n {
        0 => a,
        _ => fib(b, a + b, n - 1),
    }
}
fn fib_mid(n: felt252) {
    match n {
        0 => (),
        _ => {
            fib(0, 1, 500);
            fib_mid(n - 1);
        },
    }
}
fn main(a: felt252) {
    fib_mid(100);
}
