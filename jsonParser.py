from dis import Instruction
import json
import re
import collections
from disassembler import decodeInstruction

jsonType = None

def decodeToJson(decoded):
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

def extractRetAndArgs(json_data, functionOffset):
    identifiers = json_data["identifiers"] if ("identifiers" in json_data) else json_data["program"]["identifiers"]
    functionIdentifiers = {}
    args = None
    ret = None
    ## Get arguments and return value of function
    for offset in functionOffset:
        functionName = functionOffset[offset]
        functionIdentifiers[functionName] = {}
        functionIdentifiers[functionName]["args"] = {}
        functionIdentifiers[functionName]["return"] = {}
        if (functionName + ".Args" in identifiers and "members" in identifiers[functionName + ".Args"]):
            args = identifiers[functionName + ".Args"]["members"]
            if (functionName + ".ImplicitArgs" in identifiers and "members" in identifiers[functionName + ".ImplicitArgs"]):
                args.update(identifiers[functionName + ".ImplicitArgs"]["members"])
            for argument in args:
                argsData = identifiers[functionName + ".Args"]["members"][argument]
                functionIdentifiers[functionName]["args"][argsData["offset"]] = {}
                functionIdentifiers[functionName]["args"][argsData["offset"]][argument] = argsData["cairo_type"]
            functionIdentifiers[functionName]["args"] = dict(collections.OrderedDict(sorted(functionIdentifiers[functionName]["args"].items())))
        if (functionName + ".Return" in identifiers and "members" in identifiers[functionName + ".Return"]):
            ret = identifiers[functionName + ".Return"]["members"]
            for argument in ret:
                retData = identifiers[functionName + ".Return"]["members"][argument]
                functionIdentifiers[functionName]["return"][retData["offset"]] = {}
                functionIdentifiers[functionName]["return"][retData["offset"]][argument] = retData["cairo_type"]
            functionIdentifiers[functionName]["return"] = dict(collections.OrderedDict(sorted(functionIdentifiers[functionName]["return"].items())))
    return functionIdentifiers

def extractData(path):
    data = []
    functionOffset = {}
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
        instructionLocations = debugInfo["instruction_locations"]
        actualFunction = ""
        ## Get function name and put it in dictionnary with offset as key
        for offset in instructionLocations:
            # Link instruction and offset to a function
            functionName = instructionLocations[offset]["accessible_scopes"][1]
            if (actualFunction != functionName):
                functionOffset[offset] = functionName
                actualFunction = functionName
        functionIdentifiers = extractRetAndArgs(json_data, functionOffset)

    else:
        debugInfo = json_data["abi"]
        id = 0
        for dictionnary in debugInfo:
            if (dictionnary["type"] == "event" or dictionnary["type"] == "function"):
                functionOffset[str(id)] = dictionnary["name"]
                id += 1
    
    # tofix : why do we need this ?
    if data[len(data) - 1] != 2345108766317314046:
        data.append(2345108766317314046)
    return (data, functionOffset, functionIdentifiers)


def parseToJson(path):
    data, functionOffset, functionIdentifiers = extractData(path)
    size = len(data)
    offset = 0
    bytecodesToJson = {}
    actualFunction = ""
    incr = 0
    while (offset < size):
        if ((jsonType != "get_code" and str(offset) in functionOffset) or (jsonType == "get_code" and actualFunction not in bytecodesToJson)):
            actualFunction = functionOffset[str(offset)] if (jsonType != "get_code") else f"function 0"
            bytecodesToJson[actualFunction] = {}
            bytecodesToJson[actualFunction]["data"] = functionIdentifiers[actualFunction]
            bytecodesToJson[actualFunction]["instruction"] = {}
            #bytecodesToJson[actualFunction].update(functionIdentifiers[actualFunction])
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