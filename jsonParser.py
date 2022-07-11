import json
import re
from disassembler import decodeInstruction

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

def parseToJson(path, contract_type="cairo"):
    with path[0] as f:
        json_data = json.load(f)

    data = [int(bytecode, 16) for bytecode in json_data["data"]] if (contract_type == "cairo") else\
        [int(bytecode, 16) for bytecode in json_data["program"]["data"]] 

    debugInfo = json_data["debug_info"]
    instructionLocations = debugInfo["instruction_locations"]
    functionOffset = {}
    actualFunction = ""
    for offset in instructionLocations:
        # Link instruction and offset to a function
        functionName = instructionLocations[offset]["accessible_scopes"][1]
        if (actualFunction != functionName):
            functionOffset[offset] = functionName
            actualFunction = functionName

    # tofix : why do we need this ?
    if data[len(data) - 1] != 2345108766317314046:
        data.append(2345108766317314046)

    size = len(data)
    offset = 0
    bytecodesToJson = {}
    actualFunction = ""
    while (offset < size):
        if (str(offset) in functionOffset):
            actualFunction = functionOffset[str(offset)]
            bytecodesToJson[actualFunction] = {}
        try:
            decoded = decodeInstruction(data[offset])
            key = str(offset)
            bytecodesToJson[actualFunction][key] = {}
            bytecodesToJson[actualFunction][key][hex(data[offset])] = decodeToJson(str(decoded))
            offset += 1
        except AssertionError:
            #l[offset + 1] -> imm value
            decoded = decodeInstruction(data[offset], data[offset + 1])
            key = str(offset)
            bytecodesToJson[actualFunction][key] = {}
            bytecodesToJson[actualFunction][key][hex(data[offset])] = decodeToJson(str(decoded))
            offset += 2
    
    print("\n", json.dumps(bytecodesToJson, indent=3))
    return bytecodesToJson