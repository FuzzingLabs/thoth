# cairo_disassembler

Development: Cairo Bytecode Disassembler
Expected features: Bytecode to instructions, CFG graph, Call graph, Analytics 


## Compilation

```sh
cairo-compile tests/cairo_files/if_negative.cairo --output tests/json_files/if_negative.json

starknet-compile the_contract.cairo  --output contract_compiled.json  --abi contract_abi.json
```


## run the bytecode
```sh
cairo-run --program=tests/json_files/if_negative.json --print_output --layout=small
```

to see the offset and the bytecode :

```sh
cairo-run --program=tests/json_files/if_negative.json --print_memory 
```

# Run disassembler

Temporary, the disassembler is not a python package, the first release should be a package to install with pip.

```sh
python3 __main__.py cairo -file tests/json_files/if_negative.json
```

# Run testsuit
```sh
python3 tests/regression_test.py
```
