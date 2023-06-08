## Symbolic bounded model checker

The symbolic execution of the sierra can be used to formally verify a contract using the `thoth-checker` app.

It is possible to write the assertions directly in your Cairo program using the `assert()` function. thoth-checker will automatically test all functions whose name begins with `thoth_test`.

### Successful check

Here we have written an assertion to formally check that there can be a result where the sum of `a` and `b` is 10.

```rs
fn thoth_test_sum(mut a: felt252, mut b: felt252) {
   let sum = a + b;
   assert(sum == 10, '');
}
```

We compile this Cairo code into Sierra using `cairo-compile`

```
cairo-compile ./test_checker.cairo ./test_checker.sierra -r
```

It is now possible to verify the assertion using `thoth-checker`

```
$ ~ thoth-checker -f ./test_checker.sierra

[+] Thoth Symbolic bounded model checker

[PASS] test_checker::test_checker::thoth_test_sum (test 1/1, time: 0.07s, paths: 4)
```

This assertion is therefore proven true using `thoth-checker`.

### Failed check

Here we have written an assertion to formally check that there can be a result where `a * 2` is equal to 11, which is impossible.

```rs
fn thoth_test_product(mut a: felt252) {
   let c = a * 2;
   assert(c == 11, '');
}
```

We compile this Cairo code into Sierra using `cairo-compile`

```
cairo-compile ./test_checker_2.cairo ./test_checker_2.sierra -r
```

It is now possible to verify the assertion using `thoth-checker`

```
$ ~ thoth-checker -f ./test_checker_2.sierra

[+] Thoth Symbolic bounded model checker

[FAIL] test_checker::test_checker::thoth_test_product (test 1/1, time: 0.02s, paths: 4)
```

We have therefore formally proved that this assertion is false.

### Test a contract function

Here we have written an assertion to formally check that the `sum` variable is equal to 3.

```rs
fn add(mut a: felt252, mut b: felt 252) -> felt252 {
   let c = a + b;
   c
}

fn thoth_test_sum() {
   let sum = add(1, 2);
   assert(sum == 3, '');
}
```

We compile this Cairo code into Sierra using `cairo-compile`

```
cairo-compile ./test_checker_3.cairo ./test_checker_3.sierra -r
```

It is now possible to verify the assertion using `thoth-checker`

```
$ ~ thoth-checker -f ./test_checker_3.sierra

[+] Thoth Symbolic bounded model checker

test_checker::test_checker::thoth_test_sum SUCCESS (test 1/1, time: 0.07s, paths: 4)
```

### Test a contract function - 2

Here we have written an assertion to formally check that the `sum` variable is equal to 6.

```rs
fn add(mut a: felt252, mut b: felt 252) -> felt252 {
   let c = a + b;
   c
}

fn thoth_test_sum() {
   let sum = add(1, 2);
   let sum2 = add(sum, 3)
   assert(sum2 == 6, '');
}
```

We compile this Cairo code into Sierra using `cairo-compile`

```
cairo-compile ./test_checker_4.cairo ./test_checker_4.sierra -r
```

It is now possible to verify the assertion using `thoth-checker`

```
$ ~ thoth-checker -f ./test_checker_4.sierra

[+] Thoth Symbolic bounded model checker

test_checker::test_checker::thoth_test_sum (test 1/1, time: 0.07s, paths: 4)
```

### Test a contract function with a loop

Here we have written an assertion to formally check that the `sum` variable is equal to 2.

**The symbolic bounded model checker can run for too long if used in a function with a loop because of the explosion in the number of paths.**

```rs
fn add(mut a: felt252, mut b: felt 252) -> felt252 {
   let c = a + b;
   c
}

fn thoth_test_sum() {
   let counter = 0;
   let sum = 0;
   
   loop {
         sum = add(sum, 1);
         counter = counter + 1;
         
         if counter == 2 {
            break;
         }
   }
   assert(sum == 2, '');
}
```

We compile this Cairo code into Sierra using `cairo-compile`

```
cairo-compile ./test_checker_5.cairo ./test_checker_5.sierra -r
```

### Test a contract function with a loop (fibonacci)

Here we have written an assertion to formally check that the `fib` variable is equal to 2.

```rs
fn fib(mut a: felt252, mut b: felt252, mut n: felt252) -> felt252 {
    loop {
        if n == 0 {
            break a;
        }
        n = n - 1;
        let temp = b;
        b = a + b;
        a = temp;
    }
}

fn thoth_test_fib() {
   let fib = fib(1, 1, 2);
   assert(fib == 2, '');
}
```

We compile this Cairo code into Sierra using `cairo-compile`

```
cairo-compile ./test_checker_6.cairo ./test_checker_6.sierra -r
```

It is now possible to verify the assertion using `thoth-checker`

```
$ ~ thoth-checker -f ./test_checker_6.sierra

[+] Thoth Symbolic bounded model checker

test_checker::test_checker::thoth_test_sum (test 1/1, time: 0.92s, paths: 16)
```
