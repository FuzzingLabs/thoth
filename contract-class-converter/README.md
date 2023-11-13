## Convert contract class JSON files to Sierra files 

When you compile a cairo contract with `starknet-compile`, you obtain a ContractClass JSON file. To convert this ContractClass file into a sierra file, you need to use `contract-class-converter`. 

#### Run the tool 

```
cargo run --release <path_to_your_contract_class_file>  > sierra_file.sierra
```

#### Analyze the sierra file

Now you can analyze the sierra file using [thoth-sierra](https://github.com/FuzzingLabs/thoth/tree/master/sierra).