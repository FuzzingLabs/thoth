# Thoth, the Cairo/Starknet bytecode analyzer, disassembler and decompiler
<img src="./tests/coverage.svg"/> <img src ="https://img.shields.io/badge/python-3.10-blue.svg"/>

Thoth (pronounced "taut" or "toss") is a Cairo/Starknet analyzer, disassembler & decompiler written in Python 3. Thoth's features include the generation of the call graph, the control-flow graph (CFG) and the data-flow graph for a given [Sierra file](/sierra/README.md) or Cairo/Starknet compilation artifact.

Learn more about Thoth internals here: [Demo video](https://www.youtube.com/watch?v=T0KvG8Zps6I), [StarkNetCC 2022 slides](https://fuzzinglabs.com/wp-content/uploads/2022/11/Thoth_cairo_analyzer_starknetcc_lisbon_2022.pdf)

## Features
- **Remote & Local**: Thoth can both analyze contracts deployed on Mainnet/Goerli and compiled locally on your machine. 
- **[Decompiler](#decompile-the-contracts-compilation-artifact-json)**: Thoth can convert assembly into decompiled code with SSA (Static Single Assignment)  
- **[Call Flow analysis](#print-the-contracts-call-graph)**: Thoth can generate a **Call Flow Graph** 
- **[Static analysis](#run-the-static-analysis)**: Thoth can run various **analyzers** of different types (*security*/*optimization*/*analytics*) on the contract
- **[Symbolic execution](#use-the-symbolic-execution)**: Thoth can use the **symbolic execution** to find the right variables values to get through a specific path in a function and also automatically **generate test cases** for a function.
- **[Data Flow analysis](#print-the-contracts-data-flow-graph-dfg)**: Thoth can generate a **Data Flow Graph** (DFG) for each function
- **[Disassembler](#disassemble-the-contracts-compilation-artifact-json)**: Thoth can translate bytecode into assembly representation
- **[Control Flow analysis](#print-the-contracts-control-flow-graph-cfg)**: Thoth can generate a **Control Flow Graph** (CFG)
- **[Sierra files analysis](/sierra/README.md)** : Thoth can analyze **Sierra** files 

## Installation
 
```
sudo apt install graphviz
git clone https://github.com/FuzzingLabs/thoth && cd thoth
pip install .
thoth -h
```

## Decompile the contract's compilation artifact (JSON)

``` python
# Remote contrat deployed on starknet (mainnet/goerli)
thoth remote --address 0x0323D18E2401DDe9aFFE1908e9863cbfE523791690F32a2ff6aa66959841D31D --network mainnet -d
# Local contract compiled locally (JSON file)
thoth local tests/json_files/cairo_0/cairo_test_addition_if.json -d
```

Example 1 with strings:
<p align="center">
	<b> source code </b></br>
	<img src="/images/thoth/thoth_decompile_sourcecode.png"/></br>
	<b> decompiler code </b></br>
	<img src="/images/thoth/thoth_decompile.png"/></br>
</p>
Example 2 with function call:
<p align="center">
	<b> source code </b></br>
	<img src="/images/thoth/thoth_decompile_sourcecode_2.png"/></br>
	<b> decompiler code </b></br>
	<img src="/images/thoth/thoth_decompile_2.png"/></br>
</p>


## Print the contract's call graph 

The call flow graph represents calling relationships between functions of the contract. We tried to provide a maximum of information, such as the entry-point functions, the imports, decorators, etc.

``` python
thoth local tests/json_files/cairo_0/cairo_array_sum.json -call -view
# For a specific output format (pdf/svg/png):
thoth local tests/json_files/cairo_0/cairo_array_sum.json -call -view -format png
```
The output file (pdf/svg/png) and the dot file are inside the `output-callgraph` folder.
If needed, you can also visualize dot files online using [this](https://dreampuf.github.io/GraphvizOnline/) website. The legend can be found [here](images/callgraph_legend.png).

<p align="center">
	<img src="/images/thoth/thoth_callgraph_simple.png"/>
</p>

A more complexe callgraph:
<p align="center">
	<img src="/images/thoth/starknet_get_full_contract_l2_dai_bridge.gv.png"/>
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
|**Test cases generator**|`tests`|Automatically generate test cases for each function of the contract|Informational|High|Analytics|
|**Assignations**|`assignations`|List of variables assignations|Informational|High|Optimization|
|**Integer overflow**|`int_overflow`|Detect direct integer overflow/underflow|High (direct) / Medium (indirect)|Medium|Security|
|**Function naming**|`function_naming`|Detect functions names that are not in snake case|Informational|High|Security|
|**Variable naming**|`variable_naming`|Detect variables names that are not in snake case|Informational|High|Security|

#### Run all the analyzers
``` python
thoth local tests/json_files/cairo_0/cairo_array_sum.json -a
```

#### Selects which analyzers to run
``` python
thoth local tests/json_files/cairo_0/cairo_array_sum.json -a erc20 erc721
```

#### Only run a specific category of analyzers
``` python
thoth local tests/json_files/cairo_0/cairo_array_sum.json -a security
thoth local tests/json_files/cairo_0/cairo_array_sum.json -a optimization
thoth local tests/json_files/cairo_0/cairo_array_sum.json -a analytics
```

#### Print a list of all the availables analyzers
```
thoth local tests/json_files/cairo_0/cairo_array_sum.json --analyzers-help
```

## Use the symbolic execution 

#### Using the command-line

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
	<img src="/images/thoth/thoth_symbolic_execution_source.png"/></br>
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

#### With a configuration file

It is also possible to use symbolic execution with a YAML configuration file.

An example with this `config.yaml` file:
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

## Print the contract's data-flow graph (DFG)

``` python
thoth local tests/json_files/cairo_0/cairo_double_function_and_if.json -dfg -view
# For a specific output format (pdf/svg/png):
thoth local tests/json_files/cairo_0/cairo_double_function_and_if.json -dfg -view -format png
# For tainting visualization:
thoth remote --address 0x069e40D2c88F479c86aB3E379Da958c75724eC1d5b7285E14e7bA44FD2f746A8 -n mainnet  -dfg -view --taint
```
The output file (pdf/svg/png) and the dot file are inside the `output-dfg` folder.

<p align="center">
	<img src="/images/thoth/thoth_dataflow_graph.png"/>
</p>

<p align="center">
	<img src="/images/thoth/thoth_dfg_tainting.png"/>
</p>

## Disassemble the contract's compilation artifact (JSON)

``` python
# Remote contrat deployed on starknet (mainnet/goerli)
thoth remote --address 0x0323D18E2401DDe9aFFE1908e9863cbfE523791690F32a2ff6aa66959841D31D --network mainnet -b
# Local contract compiled locally (JSON file)
thoth local tests/json_files/cairo_0/cairo_array_sum.json -b
# To get a pretty colored version:
thoth local tests/json_files/cairo_0/cairo_array_sum.json -b -color
# To get a verbose version with more details about decoded bytecodes:
thoth local tests/json_files/cairo_0/cairo_array_sum.json -vvv
```

<p align="center">
	<img src="/images/thoth/thoth_disas_color.png"/>
</p>

## Print the contract's control-flow graph (CFG)

``` python
thoth local tests/json_files/cairo_0/cairo_double_function_and_if.json -cfg -view
# For a specific function:
thoth local tests/json_files/cairo_0/cairo_double_function_and_if.json -cfg -view -function "__main__.main"
# For a specific output format (pdf/svg/png):
thoth local tests/json_files/cairo_0/cairo_double_function_and_if.json -cfg -view -format png
```
The output file (pdf/svg/png) and the dot file are inside the `output-cfg` folder.

<p align="center">
	<img src="/images/thoth/cairo_double_function_and_if_cfg.png"/>
</p>

# F.A.Q

## How to find a Cairo/Starknet compilation artifact (json file)?

Thoth supports cairo and starknet compilation artifact (json file) generated after compilation using `cairo-compile` or `starknet-compile`. Thoth also support the json file returned by: `starknet get_full_contract`.

## How to run the tests?

```
python3 tests/test.py
```

## How to build the documentation?

``` python
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

``` cairo
%lang starknet

from starkware.cairo.common.cairo_builtins import HashBuiltin

@storage_var
func balance() -> (res : felt):
end
```

# Acknowledgments

Thoth is inspired by a lot of differents security tools developped by friends such as: [Octopus](https://github.com/FuzzingLabs/octopus), [Slither](https://github.com/crytic/slither), [Mythril](https://github.com/ConsenSys/mythril), etc.

# License

Thoth is licensed and distributed under the AGPLv3 license. [Contact us](mailto:contact@fuzzinglabs.com) if you're looking for an exception to the terms.
