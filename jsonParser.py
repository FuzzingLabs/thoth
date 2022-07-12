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

def parseToJson(path):
    with path[0] as f:
        json_data = json.load(f)

    data = []
    if ("data" in json_data):
        data = [int(bytecode, 16) for bytecode in json_data["data"]]
        jsonType = "cairo"
    elif ("program" in json_data):
        data = [int(bytecode, 16) for bytecode in json_data["program"]["data"]] 
        jsonType = "starknet"
    else:
        data = [int(bytecode, 16) for bytecode in json_data["bytecode"]]
        jsonType = "get_code"
    
    functionOffset = {}
    
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

    size = len(data)
    offset = 0
    bytecodesToJson = {}
    actualFunction = ""
    id = 0
    old_id = 0

    while (offset < size):
        if (jsonType != "get_code" and str(offset) in functionOffset):
            actualFunction = functionOffset[str(offset)]
            bytecodesToJson[actualFunction] = {}

        elif (jsonType == "get_code" and actualFunction not in bytecodesToJson):
            actualFunction = f"function 0"
            bytecodesToJson[actualFunction] = {}
        try:
            id += 1
            decoded = decodeInstruction(data[offset])
            key = str(offset)
            bytecodesToJson[actualFunction][key] = {}
            bytecodesToJson[actualFunction][key][hex(data[offset])] = decodeToJson(str(decoded))
            """if (jsonType == "get_code" and "RET" in bytecodesToJson[actualFunction][key][hex(data[offset])]["opcode"]):
                old_id = id
                id += 1"""
            offset += 1
        except AssertionError:
            old_id += 1
            #l[offset + 1] -> imm value
            decoded = decodeInstruction(data[offset], data[offset + 1])
            key = str(offset)
            bytecodesToJson[actualFunction][key] = {}
            bytecodesToJson[actualFunction][key][hex(data[offset])] = decodeToJson(str(decoded))
            """if (jsonType == "get_code" and "RET" in bytecodesToJson[actualFunction][key][hex(data[offset])]["opcode"]):
                old_id = id
                id += 1 += 1"""
            offset += 2
    return bytecodesToJson