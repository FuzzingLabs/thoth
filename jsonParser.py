#!/usr/bin/env python3

import json
import re
import collections
from instruction import decodeInstruction

jsonType = None

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

def extractFunctionPrototype(json_data, func_offset):
    """
    Get the informations about arguments/return/decorators
    """
    identifiers_data = json_data["identifiers"] if ("identifiers" in json_data) else json_data["program"]["identifiers"]
    identifiers_name = [".ImplicitArgs", ".Args", ".Return"]
    func_identifiers = {}
    data = None
    # get entry_point offsets
    entry_points = []
    entry_points_by_type = json_data["entry_points_by_type"] if ("entry_points_by_type" in json_data) else None
    if entry_points_by_type:
        for entry_type in entry_points_by_type.values():
            entry_points += [str(int(entry['offset'], base=16)) for entry in entry_type]

    ## Get arguments and return value of function
    for offset in func_offset:
        func_name = func_offset[offset]
        identifiers = func_identifiers[func_name] = {}
                
        # get func args values
        for identifier_name in identifiers_name:
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

def extractData(path):
    """
    Return the good dictionary that contains the instructions for the Bytecodes and the Identifiers for the return/args informations
    """
    data = []
    func_offset = {}
    
    with path[0] as f:
        json_data = json.load(f)

    if ("data" in json_data):
        data = [int(bytecode, 16) for bytecode in json_data["data"]]
        jsonType = "cairo"
    elif ("program" in json_data):
        data = [int(bytecode, 16) for bytecode in json_data["program"]["data"]] 
        jsonType = "starknet"
    else:
        data = [int(bytecode, 16) for bytecode in json_data["bytecode"]]
        jsonType = "get_code"

    if (jsonType != "get_code"):
        debugInfo = json_data["debug_info"] if ("debug_info" in json_data) else  json_data["program"]["debug_info"]
        instr_locations = debugInfo["instruction_locations"]
        actualFunction = ""
        ## Get function name and put it in dictionnary with offset as key
        for offset in instr_locations:
            # Link instruction and offset to a function
            func_name = instr_locations[offset]["accessible_scopes"][-1]
            if (actualFunction != func_name):
                func_offset[offset] = func_name
                actualFunction = func_name
        func_identifiers = extractFunctionPrototype(json_data, func_offset)

    else:
        debugInfo = json_data["abi"]
        id = 0
        for dictionnary in debugInfo:
            if (dictionnary["type"] == "event" or dictionnary["type"] == "function"):
                func_offset[str(id)] = dictionnary["name"]
                id += 1
    
    if data[len(data) - 1] != 2345108766317314046:
        data.append(2345108766317314046)
    return (data, func_offset, func_identifiers)


def parseToJson(path):
    """
    Get bytecodes and decode it.
    Also get informations about return values, arguments and decorators
    Build a generic Json.
    """
    data, func_offset, func_identifiers = extractData(path)
    size = len(data)
    offset = 0
    bytecodesToJson = {}
    actualFunction = ""
    incr = 0
    while (offset < size):
        if ((jsonType != "get_code" and str(offset) in func_offset) or (jsonType == "get_code" and actualFunction not in bytecodesToJson)):
            actualFunction = func_offset[str(offset)] if (jsonType != "get_code") else f"function 0"
            bytecodesToJson[actualFunction] = {}
            bytecodesToJson[actualFunction]["data"] = func_identifiers[actualFunction]
            bytecodesToJson[actualFunction]["instruction"] = {}
        try:
            decoded = decodeInstruction(data[offset])
            incr = 1
        except AssertionError:
            #l[offset + 1] -> imm value
            decoded = decodeInstruction(data[offset], data[offset + 1])
            incr = 2
        key = str(offset)
        bytecodesToJson[actualFunction]["instruction"][key] = {}
        bytecodesToJson[actualFunction]["instruction"][key][hex(data[offset])] = decodeToJson(str(decoded))
        offset += incr
    return bytecodesToJson