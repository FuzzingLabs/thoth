# Symbolic Execution

*thoth-sierra* has a symbolic execution feature that works in the same way as in *thoth*.

For example when decompiling a simple program in Sierra using the *thoth-sierra* decompiler
```
thoth-sierra -f ./tests/sierra_files/symbolic_execution_test.sierra -d
```

We get this result
```js
// Function 1
func symbolic::symbolic::symbolic_execution_test (v0: felt252, v1: felt252, v2: felt252, v3: felt252) -> ()
{
        v4 = felt252_const<102>()
        v5 = felt252_sub(v0, v4)
        v5 = store_temp<felt252>(v5)
        if (felt252_is_zero(v5) == 0) {
                branch_align()
                drop<NonZero<felt252>>(v6)
        } else {
                branch_align()
        }
        v7 = felt252_const<117>()
        v8 = felt252_sub(v1, v7)
        v8 = store_temp<felt252>(v8)
        if (felt252_is_zero(v8) == 0) {
                branch_align()
                drop<NonZero<felt252>>(v9)
        } else {
                branch_align()
        }
        v10 = felt252_const<122>()
        v11 = felt252_sub(v2, v10)
        v11 = store_temp<felt252>(v11)
        if (felt252_is_zero(v11) == 0) {
                branch_align()
                drop<NonZero<felt252>>(v12)
        } else {
                branch_align()
        }
        v13 = felt252_const<122>()
        v14 = felt252_sub(v3, v13)
        v14 = store_temp<felt252>(v14)
        if (felt252_is_zero(v14) == 0) {
                branch_align()
                drop<NonZero<felt252>>(v15)
        } else {
                branch_align()
        }
        v16 = felt252_const<0>()
        v17 = store_temp<felt252>(v16)
        return (v17)
}
```

We can use the symbolic execution engine of *thoth-sierra* to get the arguments values to pass to this function to satisfy all the conditions in the following way

```python
thoth-sierra -f ./tests/sierra_files/symbolic_execution_test.sierra --symbolic -function symbolic::symbolic::symbolic_execution_test -solve v0 v1 v2 v3 -constraint v5==0 v8==0 v11==0 v14==0                
v0: 102
v1: 117
v2: 122
v3: 122
```