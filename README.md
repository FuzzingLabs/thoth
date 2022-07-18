# Thoth

Thoth is a Cairo/starknet bytecode disassembler written in Python 3.

## Installation

```sh
pip install .
```

## Disassemble a Cairo file

```sh
thoth -f tests/json_files/cairo_array_sum.json
```

To get a pretty colored version:

```sh
thoth -f tests/json_files/cairo_array_sum.json -color
```
<p align="center">
	<img src="/images/thoth_disas_color.png"/>
</p>

To get a verbose version with more details about decoded bytecodes:
```sh
thoth -f tests/json_files/cairo_array_sum.json -vvv
```

## Print Call Flow Graph 

```sh
thoth -f tests/json_files/cairo_array_sum.json -call
```
Example of a more complexe callgraph [here](images/starknet_get_full_contract_l2_dai_bridge.gv.png).

<p align="center">
	<img src="/images/thoth_callgraph_simple.png"/>
</p>

Legend: TODO


For a specific output format:
```sh
thoth -f tests/json_files/cairo_array_sum.json -call -format [pdf/svg/png]
```

## Print CFG 

```sh
thoth -f tests/json_files/cairo_array_sum.json -cfg
```

<p align="center">
	<img src="/images/cairo_array_sum.gv.png"/>
</p>

For a specific function:
```sh
thoth -f tests/json_files/cairo_array_sum.json -cfg -function FUNCTION_NAME
```
For a specific output format:
```sh
thoth -f tests/json_files/cairo_array_sum.json -cfg -format [pdf/svg/png]
```

## Get analytics
```sh
thoth -f tests/json_files/cairo_array_sum.json -analytics
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

# License

Thoth is licensed and distributed under the AGPLv3 license. [Contact us](mailto:contact@fuzzinglabs.com) if you're looking for an exception to the terms.
