# ---------------------------------
# Imports and Costants
# ---------------------------------

from sre_constants import ASSERT
from starkware.cairo.lang.compiler.encode import *
from starkware.cairo.lang.compiler.instruction import Instruction
from starkware.cairo.lang.compiler.instruction import decode_instruction_values as CairoDecode
from starkware.cairo.lang.compiler.instruction_builder import *
from starkware.cairo.lang.compiler.parser import *
import json
import logging
import re

# ---------------------------------
# Function which decode an encoded 
# instruction and it possible immediate value
# ---------------------------------

def decodeInstruction(encoding: int, imm: Optional[int] = None) -> Instruction:
    """
    Given 1 or 2 integers representing an instruction, returns the Instruction.
    If imm is given for an instruction with no immediate, it will be ignored.
    """
    flags, off0_enc, off1_enc, off2_enc = decode_instruction_values(encoding)

    # Get dst_register.
    dst_register = Register.FP if (flags >> DST_REG_BIT) & 1 else Register.AP

    # Get op0_register.
    op0_register = Register.FP if (flags >> OP0_REG_BIT) & 1 else Register.AP

    # Get op1.
    op1_addr = {
        (1, 0, 0): Instruction.Op1Addr.IMM,
        (0, 1, 0): Instruction.Op1Addr.AP,
        (0, 0, 1): Instruction.Op1Addr.FP,
        (0, 0, 0): Instruction.Op1Addr.OP0,
    }[(flags >> OP1_IMM_BIT) & 1, (flags >> OP1_AP_BIT) & 1, (flags >> OP1_FP_BIT) & 1]

    if op1_addr is Instruction.Op1Addr.IMM:
        assert imm is not None, "op1_addr is Op1Addr.IMM, but no immediate given"
    else:
        imm = None

    # Get pc_update.
    pc_update = {
        (1, 0, 0): Instruction.PcUpdate.JUMP,
        (0, 1, 0): Instruction.PcUpdate.JUMP_REL,
        (0, 0, 1): Instruction.PcUpdate.JNZ,
        (0, 0, 0): Instruction.PcUpdate.REGULAR,
    }[(flags >> PC_JUMP_ABS_BIT) & 1, (flags >> PC_JUMP_REL_BIT) & 1, (flags >> PC_JNZ_BIT) & 1]

    # Get res.
    res = {
        (1, 0): Instruction.Res.ADD,
        (0, 1): Instruction.Res.MUL,
        (0, 0): Instruction.Res.UNCONSTRAINED
        if pc_update is Instruction.PcUpdate.JNZ
        else Instruction.Res.OP1,
    }[(flags >> RES_ADD_BIT) & 1, (flags >> RES_MUL_BIT) & 1]

    # JNZ opcode means res must be UNCONSTRAINED.
    if pc_update is Instruction.PcUpdate.JNZ:
        assert res is Instruction.Res.UNCONSTRAINED

    # Get ap_update.
    ap_update = {
        (1, 0): Instruction.ApUpdate.ADD,
        (0, 1): Instruction.ApUpdate.ADD1,
        (0, 0): Instruction.ApUpdate.REGULAR,  # OR ADD2, depending if we have CALL opcode.
    }[(flags >> AP_ADD_BIT) & 1, (flags >> AP_ADD1_BIT) & 1]

    # Get opcode.
    opcode = {
        (1, 0, 0): Instruction.Opcode.CALL,
        (0, 1, 0): Instruction.Opcode.RET,
        (0, 0, 1): Instruction.Opcode.ASSERT_EQ,
        (0, 0, 0): Instruction.Opcode.NOP,
    }[
        (flags >> OPCODE_CALL_BIT) & 1,
        (flags >> OPCODE_RET_BIT) & 1,
        (flags >> OPCODE_ASSERT_EQ_BIT) & 1,
    ]

    # CALL opcode means ap_update must be ADD2.
    if opcode is Instruction.Opcode.CALL:
        assert ap_update is Instruction.ApUpdate.REGULAR, "CALL must have update_ap is ADD2"
        ap_update = Instruction.ApUpdate.ADD2

    # Get fp_update.
    if opcode is Instruction.Opcode.CALL:
        fp_update = Instruction.FpUpdate.AP_PLUS2
    elif opcode is Instruction.Opcode.RET:
        fp_update = Instruction.FpUpdate.DST
    else:
        fp_update = Instruction.FpUpdate.REGULAR

    return Instruction(
        off0=off0_enc - 2 ** (OFFSET_BITS - 1),
        off1=off1_enc - 2 ** (OFFSET_BITS - 1),
        off2=off2_enc - 2 ** (OFFSET_BITS - 1),
        imm=imm,
        dst_register=dst_register,
        op0_register=op0_register,
        op1_addr=op1_addr,
        res=res,
        pc_update=pc_update,
        ap_update=ap_update,
        fp_update=fp_update,
        opcode=opcode,
    )

# ---------------------------------
# Goal : get the instructions from 
# a given encoded instructions series
# ---------------------------------

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

def printData(dictResult):
    spaces = " " * 13
    prime = (2**251) + (17 * (2**192)) + 1
    for numberInstruction in dictResult.keys():
        id = numberInstruction.split("Instruction ")[1]
        print(f"\noffset {id} :" + spaces[len(id):], end="")
        for encodedInstruction in dictResult[numberInstruction].keys():
            opcode = dictResult[numberInstruction][encodedInstruction].get("opcode").split("Opcode.")[1]
            if ("ASSERT_EQ" in opcode):
                print(f"{opcode}" + spaces[len(opcode):], end="")
                dstRegister = dictResult[numberInstruction][encodedInstruction].get("dst_register").split("Register.")[1]
                offDest = dictResult[numberInstruction][encodedInstruction].get("off0")
                imm = dictResult[numberInstruction][encodedInstruction].get("imm")
                op1Addr = dictResult[numberInstruction][encodedInstruction].get("op1_addr").split("Op1Addr.")[1]
                off2 = dictResult[numberInstruction][encodedInstruction].get("off2")
                if ("IMM" in op1Addr):
                    print(f"[{dstRegister}+{offDest}], {imm}")
                else:
                    if (int(off2) < 0):
                        print(f"[{dstRegister}+{offDest}], [{op1Addr} - {off2[1:]}]")
                    else:
                        print(f"[{dstRegister}+{offDest}], [{op1Addr} + {off2}]")          
                apUpdate = dictResult[numberInstruction][encodedInstruction].get("ap_update").split("ApUpdate.")[1]
                if ("REGULAR" not in apUpdate):
                    op = list(filter(None, re.split(r'(\d+)', apUpdate)))
                    opcode = op[0]
                    val = op[1]
                    print(f"offset {id} :" + spaces[len(id):], end="")
                    print(f"{opcode}" + spaces[len(opcode):], end="")
                    print(f"AP, {val}")
            if ("NOP" in opcode):
                opcode = dictResult[numberInstruction][encodedInstruction].get("pc_update").split("PcUpdate.")[1]
                imm = dictResult[numberInstruction][encodedInstruction].get("imm")
                print(f"{opcode}" + spaces[len(opcode):], end="")
                newOffset = int(id) + int(imm)
                print(f"{newOffset}")
            if ("RET" in opcode):
                print(f"{opcode}", end="")


def analyze(path, contract_type="cairo"):
    with path[0] as f:
        json_data = json.load(f)

    l = []
    if contract_type == "cairo":
        l = [int(bytecode, 16) for bytecode in json_data["data"]]
    elif contract_type == "starknet":
        l = [int(bytecode, 16) for bytecode in json_data["program"]["data"]]
    else:
        logging.critical("Analyze: unknown contract_type")
        exit()

    # tofix : why do we need this ?
    if l[len(l)-1] != 2345108766317314046:
        l.append(2345108766317314046)

    size = len(l)
    offset = 0
    bytecodesToJson = {}
    instructionNumber = 0
    immNumber = 0
    while offset < size - 1:
        try:
            instructionNumber += 1
            #print(CairoDecode(l[offset]))
            decoded = decodeInstruction(l[offset])
            key = "Instruction " + str(offset)
            bytecodesToJson[key] = {}
            bytecodesToJson[key][hex(l[offset])] = decodeToJson(str(decoded))
            offset += 1
        except AssertionError:
            #l[offset + 1] -> imm value
            instructionNumber += 1
            immNumber += 1
            decoded = decodeInstruction(l[offset], l[offset + 1])
            key = "Instruction " + str(offset)
            bytecodesToJson[key] = {}
            bytecodesToJson[key][hex(l[offset])] = decodeToJson(str(decoded))
            offset += 2

    instructionNumber += 1
    key = "Instruction " + str(offset)
    decoded = decodeInstruction(l[offset])
    bytecodesToJson[key] = {}
    bytecodesToJson[key][hex(l[offset])] = decodeToJson(str(decoded))

    #bytecodesToJson["MetaData"] = {}
    #bytecodesToJson["MetaData"]["Instruction Number"] = instructionNumber
    #bytecodesToJson["MetaData"]["immediate value Number"] = immNumber
    
    result = json.dumps(bytecodesToJson, indent=3)
    print("\n" + result)
    printData(bytecodesToJson)