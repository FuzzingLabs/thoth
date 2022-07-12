# ---------------------------------
# Imports and Costants
# ---------------------------------

from dis import dis
from sre_constants import ASSERT
from starkware.cairo.lang.compiler.encode import *
from starkware.cairo.lang.compiler.instruction import Instruction
from starkware.cairo.lang.compiler.instruction import decode_instruction_values as CairoDecode
from starkware.cairo.lang.compiler.instruction_builder import *
from starkware.cairo.lang.compiler.parser import *
import classData
import json
import re

## Create class Function

operator = {"ADD" : "+", "MUL" : "*"}
prime = (2**251) + (17 * (2**192)) + 1

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

def analyzeGetFunctions(bytecodesToJson):
    head = None
    previous = None
    for function in bytecodesToJson:
        offsetStart = list(bytecodesToJson[function]["instruction"].keys())[0]
        offsetEnd = list(bytecodesToJson[function]["instruction"].keys())[-1]
        name = function
        instructionList = bytecodesToJson[function]["instruction"]
        args = bytecodesToJson[function]["data"]["args"]
        ret = bytecodesToJson[function]["data"]["return"]
        decorators = bytecodesToJson[function]["data"]["decorators"]
        functionClass = classData.FunctionData(offsetStart, offsetEnd, name, instructionList, args, ret, decorators)
        if (not head):
            head = functionClass
        if (previous):
            previous.nextFunction = functionClass
        previous = functionClass
    return head