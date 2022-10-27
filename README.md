# Thoth, the Cairo/Starknet bytecode analyzer, disassembler and decompiler
<img src="./tests/coverage.svg"/> <img src ="https://img.shields.io/badge/python-3.10-blue.svg"/>

Thoth (pronounced "toss") is a Cairo/Starknet analyzer, disassembler & decompiler written in Python 3. Thoth's features also include the generation of the call graph and control-flow graph (CFG) of a given Cairo/Starknet compilation artifact. [Demo video](https://www.youtube.com/watch?v=T0KvG8Zps6I)

## Installation

```sh
sudo apt install graphviz

git clone https://github.com/FuzzingLabs/thoth && cd thoth

pip install .

thoth -h
```

## Disassemble the contract's compilation artifact (json)

#### From a JSON file

```sh
thoth local tests/json_files/cairo_array_sum.json -b
```

#### From starknet 

```sh
thoth remote --address 0x0323D18E2401DDe9aFFE1908e9863cbfE523791690F32a2ff6aa66959841D31D --network mainnet -b
```

To get a pretty colored version:

```sh
thoth local tests/json_files/cairo_array_sum.json -b -color
```
<p align="center">
	<img src="/images/thoth_disas_color.png"/>
</p>

To get a verbose version with more details about decoded bytecodes:
```sh
thoth local tests/json_files/cairo_array_sum.json -vvv
```

## Decompile the contract's compilation artifact (json)


```sh
thoth local tests/json_files/cairo_test_addition_if.json -d
```
Example 1 with strings:
<p align="center">
	<b> source code </b></br>
	<img src="/images/thoth_decompile_sourcecode.png"/></br>
	<b> decompiler code </b></br>
	<img src="/images/thoth_decompile.png"/></br>
</p>
Example 2 with function call:
<p align="center">
	<b> source code </b></br>
	<img src="/images/thoth_decompile_sourcecode_2.png"/></br>
	<b> decompiler code </b></br>
	<img src="/images/thoth_decompile_2.png"/></br>
</p>

## Run the static analysis

The static analysis is performed using *analyzers* which can be either informative or security/optimization related.

|Analyzer|Command-Line argument|Description|Impact|Precision|Category|
|---|---|---|---|---|---|
|**ERC20**|`erc20`|Detect if a contract is an ERC20 Token|Informational|High|Analytics|
|**ERC721**|`erc721`|Detect if a contract is an ERC721 Token|Informational|High|Analytics|
|**Strings**|`strings`|Detect strings inside a contract|Informational|High|Analytics|
|**Functions**|`functions`|Retrieve informations about the contract's functions|Informational|High|Analytics|
|**Statistics**|`statistics`|General statistics about the contract|Informational|High|Analytics|
|**Assignations**|`assignations`|List of variables assignations|Informational|High|Optimization|
|**Integer overflow**|`int_overflow`|Detect direct integer overflow/underflow|High|Medium|Security|
|**Function naming**|`function_naming`|Detect functions names that are not in snake case|Informational|High|Security|
|**Variable naming**|`variable_naming`|Detect variables names that are not in snake case|Informational|High|Security|

```bash
# Run all the analyzers
thoth local tests/json_files/cairo_array_sum.json -a

# Selects which analyzers to run
thoth local tests/json_files/cairo_array_sum.json -a erc20 erc721

# Only run a specific category of analyzers
thoth local tests/json_files/cairo_array_sum.json -a security
thoth local tests/json_files/cairo_array_sum.json -a optimization
thoth local tests/json_files/cairo_array_sum.json -a analytics

# Print a list of all the availables analyzers
thoth local tests/json_files/cairo_array_sum.json --analyzers-help
```

## Print the contract's call graph 

The call flow graph represents calling relationships between functions of the contract. We tried to provide a maximum of information, such as the entry-point functions, the imports, decorators, etc.

```sh
thoth local tests/json_files/cairo_array_sum.json -call -view True
```
The output file (pdf/svg/png) and the dot file are inside the `output-callgraph` folder.
If needed, you can also visualize dot files online using [this](https://dreampuf.github.io/GraphvizOnline/) website. The legend can be found [here](images/callgraph_legend.png).

<p align="center">
	<img src="/images/thoth_callgraph_simple.png"/>
</p>

A more complexe callgraph:
<p align="center">
	<img src="/images/starknet_get_full_contract_l2_dai_bridge.gv.png"/>
</p>


For a specific output format (pdf/svg/png):
```sh
thoth local tests/json_files/cairo_array_sum.json -call -view True -format png
```

## Print the contract's control-flow graph (CFG)

```sh
thoth local tests/json_files/cairo_double_function_and_if.json -cfg -view True
```
The output file (pdf/svg/png) and the dot file are inside the `output-cfg` folder.

<p align="center">
	<img src="/images/cairo_double_function_and_if_cfg.png"/>
</p>

For a specific function:
```sh
thoth local tests/json_files/cairo_double_function_and_if.json -cfg -view True -function "__main__.main"
```

For a specific output format (pdf/svg/png):
```sh
thoth local tests/json_files/cairo_double_function_and_if.json -cfg -view True -format png
```

## Print the contract's data-flow graph (DFG)

```sh
thoth local tests/json_files/cairo_double_function_and_if.json -dfg -view True
```
The output file (pdf/svg/png) and the dot file are inside the `output-dfg` folder.

<p align="center">
	<img src="/images/thoth_dataflow_graph.png"/>
</p>


For a specific output format (pdf/svg/png):
```sh
thoth local tests/json_files/cairo_double_function_and_if.json -dfg -view True -format png
```

# F.A.Q

## How to find a Cairo/Starknet compilation artifact (json file)?

Thoth support cairo and starknet compilation artifact (json file) generated after compilation using `cairo-compile` or `starknet-compile`. Thoth also support the json file returned by: `starknet get_full_contract`.

## How to run the tests?

``` sh
python3 tests/test.py
```

## How to build the documentation?

```sh
# Install sphinx
apt-get install python3-sphinx

#Create the docs folder
mkdir docs & cd docs

#Init the folder
sphinx-quickstart docs

#Modify the `conf.py` file by adding
import thoth

#Generate the .rst files before the .html files
sphinx-apidoc -f -o . ..

#Generate the .html files
make html

#Run a python http server
cd _build/html; python3 -m http.server
```

## Why my bytecode is empty?

First, verify that your JSON is correct and that it contains a data section.
Second, verify that your JSON is not a contract interface.
Finally, it is possible that your contract does not generate bytecodes, for example:

```cairo
%lang starknet

from starkware.cairo.common.cairo_builtins import HashBuiltin

@storage_var
func balance() -> (res : felt):
end
```

# License

Thoth is licensed and distributed under the AGPLv3 license. [Contact us](mailto:contact@fuzzinglabs.com) if you're looking for an exception to the terms.
