use cairo_lang_starknet::contract_class::ContractClass;
use std::fs::File;
use std::io::Read;

use serde_json;

pub fn deserialize_sierra_json(json_file_path: &str) -> String {
    // Read the content of the file into a String
    let mut file_content = String::new();
    let mut file = File::open(json_file_path).expect("Could not open the specified file.");
    file.read_to_string(&mut file_content)
        .expect("Could not read the specified file.");

    // Deserialize the JSON content into a ContractClass
    let prog: ContractClass =
        serde_json::from_str(&file_content).expect("Error deserializing JSON contract class");

    let prog_sierra = prog.extract_sierra_program().unwrap();

    // Convert Sierra program to a string
    let prog_sierra_string = format!("{}", prog_sierra.to_string());

    prog_sierra_string
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn test_deserialize_sierra_json() {
        // Specify the path to the test sierra file and read its content
        let test_file_path = "./tests/files/test.sierra";
        let expected_sierra =
            fs::read_to_string(test_file_path).expect("Could not read the test file");

        // Call the deserialize_sierra_json function with the test JSON contract class file path
        let result_sierra = deserialize_sierra_json("./tests/files/test.json");

        assert_eq!(result_sierra, expected_sierra);
    }
}
