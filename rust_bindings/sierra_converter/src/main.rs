use std::fs::File;
use std::io::Read;
use cairo_lang_starknet::contract_class::{
    ContractClass
};

use serde_json;

fn main() {
    deserialize_sierra_json("./src/test.json");
}

fn deserialize_sierra_json(json_file_path: &str) {
    // Read the content of the file into a String
    let mut file_content = String::new();
    let mut file = File::open(json_file_path)
        .expect("Could not open the specified file.");
    file.read_to_string(&mut file_content)
        .expect("Could not read the specified file.");

    // Deserialize the JSON content into a ContractClass
    let prog: ContractClass = serde_json::from_str(&file_content)
        .expect("Error deserializing JSON content");

    println!("{:?}", prog);
}
