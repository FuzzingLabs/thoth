## Decompile the Sierra file

```python
 thoth-sierra -f ./tests/sierra_files/fib.sierra -d
```

<p align="center">
    <img src="/images/thoth-sierra/thoth_sierra_decompiler.png" height="500"/>
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
	<img src="/images/thoth-sierra/thoth_sierra_callgraph.png" height="400"/>
</p>

## Print the contract's Control-Flow Graph

```python
thoth-sierra -f ./tests/sierra_files/fib_box.sierra --cfg

# Output the Control-Flow Graph to a custom folder (default is ./output_callgraph)
thoth-sierra -f ./tests/sierra_files/fib_box.sierra --cfg -output_callgraph_folder ./test 

# Output the Control-Flow Graph in a specific format (pdf/png/svg, default is pdf)
thoth-sierra -f ./tests/sierra_files/fib_box.sierra --cfg --format png
```

<p align="center">
	<img src="/images/thoth-sierra/thoth_sierra_cfg.png" height="300"/>
</p>

## Run the analyzers

```
thoth local tests/json_files/cairo_array_sum.json -a
```
<p align="center">
	<img src="/images/thoth-sierra/thoth_sierra_analyzers.png" height="250"/>
</p>

