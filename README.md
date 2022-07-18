# Thoth

Thoth is a Cairo/starknet bytecode disassembler written in Python 3.

## Installation

```sh
pip install .
```

## Run disassembler

```sh
thoth -f FILENAME
```

To get a pretty version:

```sh
thoth -f FILENAME -color
```

To get a verbose version with more details about decoded bytecodes:
```sh
thoth -f FILENAME -vvv
```

## Get analytics
```sh
thoth -f FILENAME -analytics
```

## Print CFG 

```sh
thoth -f FILENAME -cfg
```
For a specific function:
```sh
thoth -f FILENAME -cfg -function FUNCTION_NAME
```
For a specific output format:
```sh
thoth -f FILENAME -cfg -format [pdf/svg/png]
```

## Print Call Flow Graph 

```sh
thoth -f FILENAME -call
```
For a specific output format:
```sh
thoth -f FILENAME -call -format [pdf/svg/png]
```

# Cairo/Starknet Compilation

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

# Run testsuit
```sh
python3 tests/test.py
```

# License

Thoth is licensed and distributed under the AGPLv3 license. [Contact us](mailto:contact@fuzzinglabs.com) if you're looking for an exception to the terms.