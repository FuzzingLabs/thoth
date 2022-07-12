import json
import re
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
        debugInfo = json_data["debug_info"]
        instructionLocations = debugInfo["instruction_locations"]
        actualFunction = ""
        for offset in instructionLocations:
            # Link instruction and offset to a function
            functionName = instructionLocations[offset]["accessible_scopes"][1]
            if (actualFunction != functionName):
                functionOffset[offset] = functionName
                actualFunction = functionName
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
    return (data, functionOffset)

def parseToJson(path):
    data, functionOffset = extractData(path)
    size = len(data)
    offset = 0
    bytecodesToJson = {}
    actualFunction = ""
    incr = 0
    while (offset < size):
        if ((jsonType != "get_code" and str(offset) in functionOffset) or (jsonType == "get_code" and actualFunction not in bytecodesToJson)):
            actualFunction = functionOffset[str(offset)] if (jsonType != "get_code") else f"function 0"
            bytecodesToJson[actualFunction] = {}
        try:
            decoded = decodeInstruction(data[offset])
            incr = 1
        except AssertionError:
            #l[offset + 1] -> imm value
            decoded = decodeInstruction(data[offset], data[offset + 1])
            incr = 2
        key = str(offset)
        bytecodesToJson[actualFunction][key] = {}
        bytecodesToJson[actualFunction][key][hex(data[offset])] = decodeToJson(str(decoded))
        offset += incr
    return bytecodesToJson