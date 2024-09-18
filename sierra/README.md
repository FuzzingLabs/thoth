> [!IMPORTANT]
> *thoth-sierra* has been rewritten in Rust in a new version: [sierra-analyzer](https://github.com/FuzzingLabs/thoth/tree/master/sierra-analyzer). It contains all the features of *thoth-sierra* (CFG, Callgraph, decompiler, detectors) and is more maintainable and efficient. 

## Decompile the Sierra file

```python
 thoth-sierra -f ./tests/sierra_files/fib.sierra -d
```

<p align="center">
    <img src="/doc/images/thoth-sierra/thoth_sierra_decompiler.png" height="500"/>
</p>

## Print the contract's Call Graph 

```python
thoth-sierra -f ./tests/sierra_files/testing.sierra --call

# Output the callgraph to a custom folder (default is ./output_callgraph)
thoth-sierra -f ./tests/sierra_files/testing.sierra --call -output_callgraph_folder ./test 

# Output the callgraph in a specific format (pdf/png/svg, default is pdf)
thoth-sierra -f ./tests/sierra_files/testing.sierra --call --format png
```

<p align="center">
	<img src="/doc/images/thoth-sierra/thoth_sierra_callgraph.png" height="400"/>
</p>

## Print the contract's Control-Flow Graph

```python
thoth-sierra -f ./tests/sierra_files/fib_box.sierra --cfg

# Output the Control-Flow Graph to a custom folder (default is ./output_callgraph)
thoth-sierra -f ./tests/sierra_files/fib_box.sierra --cfg -output_callgraph_folder ./test 

# Output the Control-Flow Graph in a specific format (pdf/png/svg, default is pdf)
thoth-sierra -f ./tests/sierra_files/fib_box.sierra --cfg --format png

# Create the CFG for a single function
thoth-sierra -f ./tests/sierra_files/minimal_contract.sierra --cfg --function minimal_contract::minimal_contract::MinimalContract::__external::empty
```

<p align="center">
	<img src="/doc/images/thoth-sierra/thoth_sierra_cfg.png" height="300"/>
</p>

## Run the analyzers

```
thoth-sierra -f tests/sierra_files/cairo_if_list.sierra -a
```
<p align="center">
	<img src="/doc/images/thoth-sierra/thoth_sierra_analyzers.png" height="250"/>
</p>

