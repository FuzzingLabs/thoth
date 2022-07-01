# cairo_disassembler

Development: Cairo Bytecode Disassembler
Expected features: Bytecode to instructions, CFG graph, Call graph, Analytics 


## Compilation

```sh
cairo-compile test_file.cairo --output a.json
starknet-compile the_contract.cairo  --output contract_compiled.json  --abi contract_abi.json
```


## run the bytecode
```sh
cairo-run --program=a.json --print_output --layout=small
```

# Run disassembler

```sh

```