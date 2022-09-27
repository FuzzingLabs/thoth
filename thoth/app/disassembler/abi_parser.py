import collections
import re
from typing import Tuple
from thoth.app.cfg.config import DEFAULT_PRIME
from thoth.app.disassembler.cairo_instruction import decode_instruction


def decode_to_json(decoded: str) -> dict:
    """Create a JSON containing the decoded bytecode

    Args:
        decoded (string): The string containing data about the bytecode

    Returns:
        Dictionnary: A dictionnary containing the data of the bytecode
    """
    data_dict = {}
    parsed = re.search(r"\((.*?)\)", decoded).group(1).split(",")
    for data in parsed:
        key = data.split("=")[0].strip()
        if "imm" not in key and "off" not in key:
            value = data.split("=")[1].split(":")[0][1:].strip()
        else:
            value = data.split("=")[1].strip()
        data_dict[key] = value
    return data_dict


def detect_type_input_json(json_data: str) -> dict:
    """Detect the type of the contract

    Args:
        json_data (Dictionnary): The input file

    Raises:
        NotImplementedError: should never be triggered

    Returns:
        String: The type of the input contract
    """
    if "data" in json_data:
        # Compiled with cairo-compile
        json_type = "cairo"
    elif "program" in json_data:
        # Compiled with starknet-compile
        # or got using `get_full_contract`
        json_type = "starknet"
    elif "bytecode" in json_data:
        # Retrive using `get_code`
        json_type = "get_code"
    else:
        raise NotImplementedError
    return json_type


def extract_function_prototype(
    function_offset: dict, identifiers_data: dict, entry_points_by_type: dict
) -> dict:
    """Build the function prototype

    Args:
        function_offset (Dictionnary): Dict containing the function offset and their name
        identifiers_data (Dictionnary): Dict containing the data needed to create the function prototype from the JSON of the contract
        entry_points_by_type (Dictionnary): Dict containing the entry points

    Returns:
        Dictionnary: Dict containing the arguments, decorators...
    """

    identifiers_name = [".ImplicitArgs", ".Args", ".Return"]
    function_identifiers = {}
    data = None
    # get entry_point offsets
    entry_points = []

    if entry_points_by_type:
        for entry_type in entry_points_by_type.values():
            entry_points += [str(int(entry["offset"], base=16)) for entry in entry_type]

    # Get arguments and return value of function
    for offset in function_offset:
        function_name = function_offset[offset]
        identifiers = function_identifiers[function_name] = {}
        # get func args values
        for identifier_name in identifiers_name:
            # first create the identifier_name even if content will be empty
            identifiers[identifier_name[1:].lower()] = {}
            function_identifier = function_name + identifier_name
            if function_identifier in identifiers_data:
                tmp = {}
                if "members" in identifiers_data[function_identifier]:
                    data = identifiers_data[function_identifier]["members"]
                    for argument in data:
                        ret_data = identifiers_data[function_identifier]["members"][argument]
                        tmp[ret_data["offset"]] = {}
                        tmp[ret_data["offset"]][argument] = ret_data["cairo_type"]
                if (
                    identifier_name == ".Return"
                    and "cairo_type" in identifiers_data[function_identifier]
                ):
                    ##Get return values and type
                    return_data = (
                        identifiers_data[function_identifier]["cairo_type"]
                        .replace("(", "")
                        .replace(")", "")
                    )
                    return_data = return_data.split(",")
                    i = 0
                    for ret_val in return_data:
                        if ":" in ret_val:
                            var_name = ret_val.split(":")[0].replace(" ", "")
                            tmp[i] = {}
                            tmp[i][var_name] = ret_val.split(":")[1].replace(" ", "")
                            i += 1
                identifiers[identifier_name[1:].lower()] = dict(
                    collections.OrderedDict(sorted(tmp.items()))
                )
        # get decorators
        if function_name in identifiers_data and "decorators" in identifiers_data[function_name]:
            identifiers["decorators"] = identifiers_data[function_name]["decorators"]

        # get entry_points
        if offset in entry_points:
            identifiers["entry_point"] = True
        # case of cairo file
        elif function_name == "__main__.main":
            identifiers["entry_point"] = True
        else:
            identifiers["entry_point"] = False
    return function_identifiers


def extract_prime(json_type: str, json_data: dict) -> int:
    """Extract the prime number from the JSON or return the default prime number

    Args:
        json_type (String): The type of the contract
        json_data (_type_): The JSON of the contract
    Returns:
        int: The prime Number
    """
    if json_type == "cairo":
        prime = int(json_data["prime"], 16)
    elif json_type == "starknet":
        prime = int(json_data["program"]["prime"], 16)
    elif json_type == "get_code":
        prime = DEFAULT_PRIME

    return prime


def extract_bytecode(json_type: str, json_data: dict) -> dict:
    """Extract the bytecode from the JSON

    Args:
        json_type (String): The type of the contract
        json_data (Dictionnary): The JSON of the contract

    Raises:
        AssertionError: Should never be triggered

    Returns:
        Dictionnary: Dict containing the bytecode
    """
    bytecode = []

    if json_type == "cairo":
        bytecode = [int(bytecode, 16) for bytecode in json_data["data"]]
    elif json_type == "starknet":
        bytecode = [int(bytecode, 16) for bytecode in json_data["program"]["data"]]
    elif json_type == "get_code":
        bytecode = [int(bytecode, 16) for bytecode in json_data["bytecode"]]
    else:
        raise AssertionError

    return bytecode


def extract_functions(json_type: str, json_data: dict) -> Tuple:
    """Get function name and put it in dictionnary with offset as key

    Args:
        json_type (String): The type of the contract
        json_data (Dictionnary): The JSON of the contract

    Returns:
        Dictionnary: Dictionnary containing the functions of the contract
    """

    function_offset = {}
    function_identifiers = {}

    if json_type != "get_code":
        identifiers_data = (
            json_data["identifiers"]
            if ("identifiers" in json_data)
            else json_data["program"]["identifiers"]
        )
        entry_points_by_type = (
            json_data["entry_points_by_type"] if ("entry_points_by_type" in json_data) else None
        )
        for key, values in identifiers_data.items():
            if values["type"] == "function":
                function_offset[str(values["pc"])] = key
        function_identifiers = extract_function_prototype(
            function_offset, identifiers_data, entry_points_by_type
        )
    else:
        function_offset["0"] = "unknown_function"
    return (function_offset, function_identifiers)


def extract_structs(json_type: str, json_data: dict) -> dict:
    """Get the structs from the JSON contract

    Args:
        json_type (String): The type of the contract
        json_data (Dictionnary): The JSON of the contract

    Returns:
        Dictionnary: Dictionnary containing the struct from the JSON contract
    """

    struct_identifiers = {}

    if json_type != "get_code":
        identifiers_data = (
            json_data["identifiers"]
            if ("identifiers" in json_data)
            else json_data["program"]["identifiers"]
        )

        for key, values in identifiers_data.items():
            if values["type"] == "struct":
                tmp = {}
                for attribut in values["members"]:
                    tmp[values["members"][attribut]["offset"]] = {}
                    tmp[values["members"][attribut]["offset"]]["attribut"] = attribut
                    tmp[values["members"][attribut]["offset"]]["cairo_type"] = values["members"][
                        attribut
                    ]["cairo_type"]
                struct_identifiers[key] = dict(collections.OrderedDict(sorted(tmp.items())))
    return struct_identifiers


def extract_builtins(json_type: str, json_data: dict) -> dict:
    """Get the builtins from the JSON contract

    Args:
        json_type (String): The type of the contract
        json_data (Dictionnary): The JSON of the contract

    Returns:
        Dictionnary: Dictionnary containing builtins from the JSON contract
    """

    if json_type == "cairo":
        builtins = json_data["builtins"]
    elif json_type == "starknet":
        builtins = json_data["program"]["builtins"]
    else:
        builtins = []
    return builtins


def extract_events(json_type: str, json_data: dict) -> dict:
    """Get the events from the JSON contract

    Args:
        json_type (String): The type of the contract
        json_data (Dictionnary): The JSON of the contract

    Returns:
        Dictionnary: Dictionnary containing the events from the JSON contract
    """

    events = {}
    if json_type == "cairo":
        # no events in cairo
        pass
    if json_type == "starknet":
        for entry in json_data["abi"]:
            if entry["type"] == "event":
                events[entry["name"]] = entry["data"]
    else:
        pass
    return events


def extract_hints(json_type: str, json_data: dict) -> dict:
    """Get the hints from the JSON contract

    Args:
        json_type (String): The type of the contract
        json_data (Dictionnary): The JSON of the contract

    Returns:
        Dictionnary: Dictionnary containing the hints from the JSON contract
    """

    hints_identifiers = {}
    if json_type != "get_code":
        instruction_data = (
            json_data["hints"] if ("hints" in json_data) else json_data["program"]["hints"]
        )
        for key, values in instruction_data.items():
            for data in values:
                if "code" in data:
                    hints_identifiers[str(key)] = data["code"]
        hints_identifiers = dict(collections.OrderedDict(sorted(hints_identifiers.items())))
    return hints_identifiers


def extract_references(json_type: str, json_data: dict) -> dict:
    """Get the references from the JSON contract

    Args:
        json_type (String): The type of the contract
        json_data (Dictionnary): The JSON of the contract

    Returns:
        Dictionnary: Dictionnary containing the references from the JSON contract
    """

    references_identifiers = {}
    if json_type != "get_code":
        identifiers_data = (
            json_data["identifiers"]
            if ("identifiers" in json_data)
            else json_data["program"]["identifiers"]
        )
        for _, values in identifiers_data.items():
            if values["type"] == "reference":
                for ref in values["references"]:
                    references_identifiers[str(ref["pc"])] = str(ref["value"])
        references_identifiers = dict(
            collections.OrderedDict(sorted(references_identifiers.items()))
        )
    return references_identifiers


def extract_labels(json_type: str, json_data: dict) -> dict:
    """Get the labels from the JSON contract

    Args:
        json_type (String): The type of the contract
        json_data (Dictionnary): The JSON of the contract

    Returns:
        Dictionnary: Dictionnary containing the labels from the JSON contract
    """

    labels_identifiers = {}
    if json_type != "get_code":
        identifiers_data = (
            json_data["identifiers"]
            if ("identifiers" in json_data)
            else json_data["program"]["identifiers"]
        )
        for key, values in identifiers_data.items():
            if values["type"] == "label":
                labels_identifiers[str(values["pc"])] = key.split(".")[-1]
        labels_identifiers = dict(collections.OrderedDict(sorted(labels_identifiers.items())))
    return labels_identifiers


def parse_to_json(json_data: str, json_type: dict) -> dict:
    """Get bytecodes and decode it.
    Also get informations about return values, arguments and decorators
    Build a generic Json.

    Args:
        json_type (String): The type of the contract
        json_data (Dictionnary): The JSON of the contract

    Returns:
        Dictionnary: Dict containing the decoded bytecodes
    """
    # get the bytecode data
    bytecode_data = extract_bytecode(json_type, json_data)
    # extract function info like offset and name
    function_offset, function_identifiers = extract_functions(json_type, json_data)
    size = len(bytecode_data)
    offset = 0
    bytecodes_to_json = {}
    actual_function = ""
    incr = 0
    while offset < size:
        if (json_type != "get_code" and str(offset) in function_offset) or (
            json_type == "get_code" and actual_function not in bytecodes_to_json
        ):
            actual_function = function_offset[str(offset)]
            bytecodes_to_json[actual_function] = {}
            bytecodes_to_json[actual_function]["data"] = (
                function_identifiers[actual_function]
                if (actual_function in function_identifiers)
                else {}
            )
            bytecodes_to_json[actual_function]["instruction"] = {}
        try:
            decoded = decode_instruction(bytecode_data[offset])
            incr = 1
        except AssertionError:
            # l[offset + 1] -> imm value
            decoded = decode_instruction(bytecode_data[offset], bytecode_data[offset + 1])
            incr = 2
        key = str(offset)
        bytecodes_to_json[actual_function]["instruction"][key] = {}
        bytecodes_to_json[actual_function]["instruction"][key][
            hex(bytecode_data[offset])
        ] = decode_to_json(str(decoded))
        offset += incr
    return bytecodes_to_json
