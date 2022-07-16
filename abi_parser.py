#!/usr/bin/env python3

import json
import re
import collections
from instruction import decode_instruction

json_type = None

def decodeToJson(decoded):
    """
    Split the return of the Decoded Bytecodes to create a dictionnary that contains the informations
    """
    dataDict = {}
    toParse = re.search(r'\((.*?)\)', decoded).group(1)
    parsed = toParse.split(",")
    for data in parsed:
        key = data.split("=")[0].strip()
        if ("imm" not in key and "off" not in key):
            value = data.split("=")[1].split(":")[0][1:].strip()
        else:
            value = data.split("=")[1].strip()
        dataDict[key] = value
    return dataDict

def extract_function_prototype(func_offset, identifiers_data, entry_points_by_type):
    """
    Get the informations about arguments/return/decorators
    """
    
    identifiers_name = [".ImplicitArgs", ".Args", ".Return"]
    func_identifiers = {}
    data = None
    # get entry_point offsets
    entry_points = []
    
    if entry_points_by_type:
        for entry_type in entry_points_by_type.values():
            entry_points += [str(int(entry['offset'], base=16)) for entry in entry_type]

    ## Get arguments and return value of function
    for offset in func_offset:
        func_name = func_offset[offset]
        identifiers = func_identifiers[func_name] = {}
                
        # get func args values
        for identifier_name in identifiers_name:
            # first create the identifier_name even if content will be empty
            identifiers[identifier_name[1:].lower()] = {}
            function_identifier = func_name + identifier_name
            if (function_identifier in identifiers_data and "members" in identifiers_data[function_identifier]):
                data = identifiers_data[function_identifier]["members"]
                
                tmp = {}
                for argument in data:
                    retData = identifiers_data[function_identifier]["members"][argument]
                    tmp[retData["offset"]] = {}
                    tmp[retData["offset"]][argument] = retData["cairo_type"]
                identifiers[identifier_name[1:].lower()] = dict(collections.OrderedDict(sorted(tmp.items())))

        # get decorators
        if (func_name in identifiers_data and "decorators" in identifiers_data[func_name]):
            identifiers["decorators"] = (identifiers_data[func_name]["decorators"])

        # get entry_points
        if offset in entry_points:
            identifiers["entry_point"] = True
        # case of cairo file
        elif func_name == "__main__.main":
            identifiers["entry_point"] = True
        else:
            identifiers["entry_point"] = False

    return func_identifiers

def detect_type_input_json(json_data):
    if ("data" in json_data):
        # compiled with cairo-compile
        json_type = "cairo"
    elif ("program" in json_data):
        # compiled with starknet-compile
        # or got using `get_full_contract`
        json_type = "starknet"
    elif ("bytecode" in json_data):
        # got using `get_code`
        json_type = "get_code"
    else:
        # should never be triggered
        raise NotImplementedError

    return json_type

def extract_bytecode(json_type, json_data):
    """
    Return the instructions for the Bytecodes
    """
    bytecode = []

    if (json_type == "cairo"):
        bytecode = [int(bytecode, 16) for bytecode in json_data["data"]]
    elif (json_type == "starknet"):
        bytecode = [int(bytecode, 16) for bytecode in json_data["program"]["data"]] 
    elif (json_type == "get_code"):
        bytecode = [int(bytecode, 16) for bytecode in json_data["bytecode"]]
    else:
        # Should never be triggered
        raise AssertionError

    if len(bytecode) == 0:
        # TODO - issue #39
        print("Sorry, no bytecode found (maybe it's a contract interface?)")
        print("Otherwise please open an issue")
        exit(1)

    return bytecode

def extract_functions(json_type, json_data):
    """
    Return the good dictionary that contains the Identifiers for the return/args informations
    """

    func_offset = {}
    func_identifiers = {}

    if (json_type != "get_code"):
        identifiers_data = json_data["identifiers"] if ("identifiers" in json_data) else json_data["program"]["identifiers"]
        entry_points_by_type = json_data["entry_points_by_type"] if ("entry_points_by_type" in json_data) else None

        ## Get function name and put it in dictionnary with offset as key
        for key, values in identifiers_data.items():
            if values["type"] == "function":
                func_offset[str(values["pc"])] = key
        func_identifiers = extract_function_prototype(func_offset, identifiers_data, entry_points_by_type)

    else:
        print("Sorry, json retrieve using `get_code` is not supported yet")
        print("Please consider using `get_full_contract` instead")
        exit(1)
        #debugInfo = json_data["abi"]
        #id = 0
        #for dictionnary in debugInfo:
        #    if (dictionnary["type"] == "event" or dictionnary["type"] == "function"):
        #        func_offset[str(id)] = dictionnary["name"]
        #        id += 1
    
    return (func_offset, func_identifiers)

def extract_struct(json_type, json_data):
    """
    Return a dictionnary that contains all the struct
    """

    struct_identifiers = {}

    if (json_type != "get_code"):
        identifiers_data = json_data["identifiers"] if ("identifiers" in json_data) else json_data["program"]["identifiers"]

        ## Get function name and put it in dictionnary with offset as key
        for key, values in identifiers_data.items():
            if values["type"] == "struct":
                tmp = {}
                for attribut in values["members"]:
                    tmp[values["members"][attribut]["offset"]] = {}
                    tmp[values["members"][attribut]["offset"]]["attribut"] = attribut
                    tmp[values["members"][attribut]["offset"]]["cairo_type"] = values["members"][attribut]["cairo_type"]
                struct_identifiers[key] = dict(collections.OrderedDict(sorted(tmp.items())))
    return struct_identifiers

def extract_builtins(json_type, json_data):
    if (json_type == "cairo"):
        builtins = [builtin for builtin in json_data["builtins"]]
    elif (json_type == "starknet"):
        builtins = [builtin for builtin in json_data["program"]["builtins"]] 
    else:
       builtins = []
    return builtins

def parseToJson(json_data, json_type):
    """
    Get bytecodes and decode it.
    Also get informations about return values, arguments and decorators
    Build a generic Json.
    """

    # get the bytecode data
    bytecode_data = extract_bytecode(json_type, json_data)
    # extract function info like offset and name
    func_offset, func_identifiers = extract_functions(json_type, json_data)

    size = len(bytecode_data)
    offset = 0
    bytecodesToJson = {}
    actualFunction = ""
    incr = 0
    while (offset < size):
        if ((json_type != "get_code" and str(offset) in func_offset) or (json_type == "get_code" and actualFunction not in bytecodesToJson)):
            actualFunction = func_offset[str(offset)] if (json_type != "get_code") else f"function 0"
            bytecodesToJson[actualFunction] = {}
            bytecodesToJson[actualFunction]["data"] = func_identifiers[actualFunction]
            bytecodesToJson[actualFunction]["instruction"] = {}
        try:
            decoded = decode_instruction(bytecode_data[offset])
            incr = 1
        except AssertionError:
            #l[offset + 1] -> imm value
            decoded = decode_instruction(bytecode_data[offset], bytecode_data[offset + 1])
            incr = 2
        key = str(offset)
        bytecodesToJson[actualFunction]["instruction"][key] = {}
        bytecodesToJson[actualFunction]["instruction"][key][hex(bytecode_data[offset])] = decodeToJson(str(decoded))
        offset += incr
    return bytecodesToJson
