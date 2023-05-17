# Symbolic Execution

Thoth integrates a symbolic execution engine powered by *z3*. It allows to solve constraints and to perform formal verification.

- [Using the command line](#using-the-command-line)
- [With a configuration file](#with-a-configuration-file)
- [For formal verification](#formal-verification)

## Using the command line

``` python
# List all assigned variables using the `assignations` analyzer or using the decompiler `-d`
thoth local tests/json_files/cairo_0/cairo_test_symbolic_execution.json -a assignations
[Optimization] Assignations 
  -  v4 = v0_x + -10
  -  v5 = v0_x + -20
  -  v6 = v1_y + -15
  -  v7 = v1_y + -25
  -  v11 = 10
  -  v12 = 20
  -  v13 = v8_output_ptr

[+] 1 analyzer was run (1 detected)

# Set variables with a custom value
thoth local tests/json_files/cairo_0/cairo_test_symbolic_execution.json --symbolic -function __main__.test_symbolic_execution -variables v0_x=1 -constraint v4==0 v6==0 -solve v1_y

# Solve the variables values with constraints 
thoth local tests/json_files/cairo_0/cairo_test_symbolic_execution.json --symbolic -function __main__.test_symbolic_execution -constraint v4==0 v6==0 -solve v0_x v1_y

v0_x: 10
v1_y: 15

# Use inequalities in the constraints 
thoth local tests/json_files/cairo_0/cairo_test_symbolic_execution.json --symbolic -function __main__.test_symbolic_execution -constraint v4!=0 v6!=0 -solve v0_x v1_y

v0_x: 11
v1_y: 16

# Use variables equalities/inequalities in the constraints 
thoth local tests/json_files/cairo_0/cairo_test_symbolic_execution.json --symbolic -function __main__.test_symbolic_execution -constraint v4!=v6 -solve v0_x v1_y

v0_x: 1

# Replace a variable using the -variable flag 
thoth local tests/json_files/cairo_0/cairo_test_symbolic_execution_3.json --symbolic -function __main__.test_symbolic_execution -constraint v13==0 v14==0 v15==0  -solve v0_f v1_u v2_z v3_z2 -variables v3_z2=26  
v0_f: 102
v1_u: 117
v2_z: 122
v3_z2: 26

# Find the right values for the variables to pass the assertions
thoth local ./tests/json_files/cairo_0/cairo_test_symbolic_execution_4.json  --symbolic -function __main__.test_symbolic_execution -solve v2 v3 v4 v5 v6 v7 v8 v9 -assertions
v2: 102
v3: 117
v4: 122
v5: 122
v6: 105
v7: 110
v8: 103
v9: 108
```

Or with a more complex case:

<p align="center">
	<b> Source code </b></br>
	<img src="/doc/images/thoth/thoth_symbolic_execution_source.png"/></br>
</p>

Solve the variables arguments values with the symbolic execution:

```python
thoth local tests/json_files/cairo_0/cairo_test_symbolic_execution_3.json --symbolic -function __main__.test_symbolic_execution -constraint v13==0 v14==0 v15==0 v16==0 v17==0 v18==0 v19==0 v20==0 v21==0 v22==0 v23==0 -solve v0_f v1_u v2_z v3_z2 v4_i v5_n v6_g v7_l v8_a v9_b v10_s

v0_f: 102
v10_s: 115
v1_u: 117
v2_z: 122
v3_z2: 122
v4_i: 105
v5_n: 110
v6_g: 103
v7_l: 108
v8_a: 97
v9_b: 98
```

## With a configuration file

It is also possible to use symbolic execution with a YAML configuration file.

For example with this `config.yaml` file:
```yaml
function: "__main__.test_symbolic_execution"
constraints: 
    - "v13>0"
    - "v14>=0"
    - "v15<=0"
solves:
   - "v0_f"
   - "v1_u" 
   - "v2_z"
   - "v3_z2"
variables:
   - "v3_z2=26"
```

We can run this command:
```python
thoth local tests/json_files/cairo_0/cairo_test_symbolic_execution_3.json --symbolic -config ./config.yaml
v0_f: 103
v1_u: 117
v2_z: 122
v3_z2: 26
```

## Formal Verification

Thoth symbolic execution can also be used for formal verification purposes.

### First example: Successful Formal Verification

For example we have this function test_formal_verification in which an amount passed as argument is subtracted from a balance of 1000.

```cairo
func test_formal_verification{range_check_ptr}(amount: felt) -> felt {
    let balance = 1000;
    
    let is_le = is_le_felt(balance, amount);
    if (is_le == 0) {
        let new_balance = balance - amount;
        return(new_balance);
    } 
    return(balance);
}
```

We want to make a formal verification that the returned balance cannot be less than 0.

First we need to decompile the JSON artifact to get the variables values.

```cairo
// Function 3
func __main__.test_formal_verification{range_check_ptr : felt}(amount : felt){
    v53 = v49_range_check_ptr
    v54 = 1000    // 0x3e8
    v55 = v50_amount
    is_le_felt(v54, v55)
    if (v55 == 0) {
        v56 = 1000    // 0x3e8
        v57 = v54
        assert v56 = v58 + v50_amount
        ret

    }
    v59 = v57
    v60 = 1000    // 0x3e8
    ret
}

```
We need to prove 2 things using **symbolic execution** to make a **formal verification**: 

- if `amount` is lower than `balance`, `new_balance` can't be < 0: 
```
!(v55 == 0 && v56 < 0)
```

- if `amount` is greater than `balance`, `balance` can't be < 0: 
```
!(v55 != 0 && v60 < 0)
```

If those two statements are verified then we proved that the returned balanced can not be negative.

#### Proving `!(v55 == 0 && v56 < 0)`

We write the following rules into our `config.yaml` file:

```yaml
function: "__main__.test_formal_verification"
constraints: 
    - "v55==0"
    - "v56<0"
solves:
   - "v50_amount"
```
And we run it:
```
thoth local ./tests/json_files/cairo_0/cairo_test_formal_verification.json --symbolic -config config.yaml

No solutions.
```

#### Proving `!(v55 != 0 && v60 < 0)`

We write the following rules into our `config.yaml` file:

```yaml
function: "__main__.test_formal_verification"
constraints: 
    - "v55!=0"
    - "v60<0"
solves:
   - "v50_amount"
```
And we run it:
```
thoth local ./tests/json_files/cairo_0/cairo_test_formal_verification.json --symbolic -config config.yaml

No solutions.
```

We proved that there is no solutions where the returned balance can be < 0.


### Second example: Failed Formal Verification

For example we have this function test_formal_verification in which an amount passed as argument is subtracted from a balance of 1000.

```cairo
func test_formal_verification{range_check_ptr}(amount: felt) -> felt {
    let balance = 1000;
    
    let is_le = is_le_felt(balance, amount);
    if (amount == 42) {
        let new_balance = - 1;
        return(new_balance);
    }
    if (is_le == 0) {
        let new_balance = balance - amount;
        return(new_balance);
    } 
    return(balance);
}
```

We want to make a formal verification that the returned balance cannot be less than 0.

First we need to decompile the JSON artifact to get the variables values.

```cairo
// Function 3
func __main__.test_formal_verification{range_check_ptr : felt}(amount : felt){
    v53 = v49_range_check_ptr
    v54 = 1000    // 0x3e8
    v55 = v50_amount
    is_le_felt(v54, v55)
    v56 = v50_amount - 42
    if (v56 == 0) {
        v57 = v54
        v58 = -1    // -0x1
        ret

    }
    if (v57 == 0) {
        v59 = 1000    // 0x3e8
        v60 = v56
        assert v59 = v61 + v50_amount
        ret

    }
    v62 = v59
    v63 = 1000    // 0x3e8
    ret
}
```
We need to prove 3 things using **symbolic execution** to make a **formal verification**: 

- if `amount` is equal to 42,  `new_balance` can't be < 0:
```
!(v56 == 0 && v58 < 0)
```

- if `amount` is lower than `balance`, `new_balance` can't be < 0: 
```
!(v57 == 0 && v59 < 0)
```

- if `amount` is greater than `balance`, `balance` can't be < 0: 
```
!(v57 != 0 && v63 < 0)
```

If those three statements are verified then we proved that the returned balanced can not be negative.

#### Proving `!(v56 == 0 && v58 < 0)`

We write the following rules into our `config.yaml` file:

```yaml
function: "__main__.test_formal_verification"
constraints: 
    - "v56==0"
    - "v58<0"
solves:
   - "v50_amount"
```
And we run it:
```
thoth local tests/json_files/cairo_0/cairo_test_formal_verification_2.json --symbolic -config config.yaml                                                          

v50_amount: 42
```

There is a solution, therefore `!(v56 == 0 && v58 < 0)` is false and the **formal verification failed.**
