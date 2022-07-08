from starkware.cairo.lang.compiler.encode import *
from starkware.cairo.lang.compiler.instruction import *
from starkware.cairo.lang.compiler.instruction_builder import *
from starkware.cairo.lang.compiler.parser import *
import json

def decode_instruction(encoding: int, imm: Optional[int] = None) -> Instruction:
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

def analyze(path):

    with open(path, mode='r') as f:

        json_data = json.load(f)

    instruction_list = []

    instruction_list = [int(x, 16) for x in json_data["data"]]

    if instruction_list[len(instruction_list)-1] != 2345108766317314046:
        instruction_list.append(2345108766317314046)

    
    size = len(instruction_list)
    offset = 0
    end_of_if_list = []
    number_of_tabs = 0

    while offset < size -1:
        try:

            instruction = decode_instruction(instruction_list[offset])
            # print(instruction)
            try:
                o = disassemble(instruction, decode_instruction(instruction_list[offset+1]))
                if o[2]:
                    end_of_if_list.append(o[2])
                print_with_tabs(o[0], number_of_tabs)
                if o[4]: number_of_tabs += 1
                offset += o[1]
                end_of_if_list, number_of_tabs = test_end_of_if_list(end_of_if_list, o[1], number_of_tabs)
            except AssertionError:
                o = disassemble(instruction, decode_instruction(instruction_list[offset+1], instruction_list[offset+2]))
                if o[2]:
                    end_of_if_list.append(o[2])
                print_with_tabs(o[0], number_of_tabs)
                if o[4]: number_of_tabs += 1
                offset += o[1]
                end_of_if_list, number_of_tabs = test_end_of_if_list(end_of_if_list, o[1], number_of_tabs)
            # except:
            #     o = disassemble(instruction)
            #     print_with_tabs(o[0], number_of_tabs)
            #     if o[4]: number_of_tabs += 1

            offset += 1
            end_of_if_list, number_of_tabs = test_end_of_if_list(end_of_if_list, 1, number_of_tabs)
        except AssertionError:
            instruction = decode_instruction(instruction_list[offset], instruction_list[offset+1])
            # print(instruction)
            
            try:
                o = disassemble(instruction, decode_instruction(instruction_list[offset+2]))
                if o[2]:
                    end_of_if_list.append(o[2])
                print_with_tabs(o[0], number_of_tabs)
                if o[4]: number_of_tabs += 1
                offset += o[1]
                end_of_if_list, number_of_tabs = test_end_of_if_list(end_of_if_list, o[1], number_of_tabs)
            except AssertionError:
                o = disassemble(instruction, decode_instruction(instruction_list[offset+2], instruction_list[offset+3]))
                if o[2]:
                    end_of_if_list.append(o[2])
                print_with_tabs(o[0], number_of_tabs)
                if o[4]: number_of_tabs += 1
                offset += o[1]
                end_of_if_list, number_of_tabs = test_end_of_if_list(end_of_if_list, o[1], number_of_tabs)
            # except:
            #     o = disassemble(instruction)
            #     print_with_tabs(o[0], number_of_tabs)
            #     if o[4]: number_of_tabs += 1
            offset += 2
            end_of_if_list, number_of_tabs = test_end_of_if_list(end_of_if_list, 2, number_of_tabs)

    # print the end of the program
    o = disassemble(decode_instruction(instruction_list[offset]))
    print_with_tabs(o[0], number_of_tabs)
    if o[4]: number_of_tabs += 1

def print_with_tabs(value, number_of_tabs=0):
    str = ""
    for i in range(0, number_of_tabs):
        str += "    "
    print(str + value)

def test_end_of_if_list(end_of_if_list, value_to_subtract, number_of_tabs):
    if len(end_of_if_list) == 0:
        return [end_of_if_list, number_of_tabs]
    for i in range(len(end_of_if_list)):
        end_of_if_list[i] = end_of_if_list[i] - value_to_subtract
        if end_of_if_list[i] <= 0:
            print_with_tabs("end", number_of_tabs-1)
    while 0 in end_of_if_list:
        end_of_if_list.remove(0)
        number_of_tabs -= 1
    while -1 in end_of_if_list:
        end_of_if_list.remove(-1)
        number_of_tabs -= 1
    return [end_of_if_list, number_of_tabs]

def disassemble(instruction, next_instruction=None):
    # if there is a second instruction given
    if(next_instruction):
        # if the instruction is an assert_equals and the next one is a no-operation
        if str(instruction.opcode) == "Opcode.ASSERT_EQ" and str(next_instruction.opcode) == "Opcode.NOP":
            if(str(next_instruction.pc_update) == "PcUpdate.JNZ"):
                return ["if " + decode_if(instruction) + " == 0 :", 2, 0, True, True]
            elif(str(next_instruction.pc_update) == "PcUpdate.JUMP_REL"):
                return [str(disassemble_one_instruction(instruction)) + "\nelse:", 2, next_instruction.imm, True, False]

    # ret ( instruction decoded + no offset to change more than usual + no end to preset )
    return [disassemble_one_instruction(instruction), 0, 0, False, False]


def disassemble_one_instruction(instruction)->str:
    # if the instruction is a return statement
    if str(instruction.opcode) == "Opcode.RET":
        return "ret"

    code = ""

    # We put the prefix
    code += "[ap" if str(instruction.dst_register) == "Register.AP" else "[fp"

    if instruction.off0 > 0:
        code += "+" + str(instruction.off0)
    elif instruction.off0 < 0:
        code += str(instruction.off0)

    code += "] = "

    
    # If the instruction is just an assignation:
    if instruction.off1 == -1 and instruction.off2 == 1:
        if str(instruction.res) == "Res.ADD":
            code += "["

            code += "ap" if str(instruction.op0_register) == "Register.AP" else "fp"

            if instruction.off1 > 0:
                code += "+" + str(instruction.off1)
            elif instruction.off1 < 0:
                code += str(instruction.off1)
            code +=  "] + "
        if str(instruction.res) == "Res.MUL":
            code += "["

            code += "ap" if str(instruction.op0_register) == "Register.AP" else "fp"

            if instruction.off1 > 0:
                code += "+" + str(instruction.off1)
            elif instruction.off1 < 0:
                code += str(instruction.off1)
            code +=  "] * "
        code += str(instruction.imm)
        if str(instruction.ap_update) == "ApUpdate.ADD1":
            code += "; ap++" 
        return code
    else:
        code += "["
        # If there is a double dereference instruction:
        if str(instruction.op1_addr) == "Op1Addr.OP0":
            code += "["

            code += "ap" if str(instruction.op0_register) == "Register.AP" else "fp"

            if instruction.off1 > 0:
                code += "+" + str(instruction.off1)
            elif instruction.off1 < 0:
                code += str(instruction.off1)
            code +=  "]"

            if instruction.off2 > 0:
                code += "+" + str(instruction.off2)
            elif instruction.off2 < 0:
                code += str(instruction.off2)
            code += "]"

            if str(instruction.ap_update) == "ApUpdate.ADD1":
                code += "; ap++" 

            return code


        # If there is only offset2
        if instruction.off1 == -1:
            code += "ap" if str(instruction.op1_addr) == "Op1Addr.AP" else "fp"
            if instruction.off2 > 0:
                code += "+" + str(instruction.off2)
            elif instruction.off2 < 0:
                code += str(instruction.off2)
            code  += "]"
            if str(instruction.ap_update) == "ApUpdate.ADD1":
                code += "; ap++" 

            return code

        # If there is only offset1
        elif instruction.off2 == 1:
            code += "ap" if str(instruction.op0_register) == "Register.AP" else "fp"
            if instruction.off1 > 0:
                code += "+" + str(instruction.off1)
            elif instruction.off1 < 0:
                code += str(instruction.off1)
            code  += "]"

        else:
            code += "ap" if str(instruction.op0_register) == "Register.AP" else "fp"
            if instruction.off1 > 0:
                code += "+" + str(instruction.off1)
            elif instruction.off1 < 0:
                code += str(instruction.off1)
            code  += "]"
    
        code += " + " if str(instruction.res) == "Res.ADD" else " * " if str(instruction.res) == "Res.MUL" else ""
        
        if str(instruction.op1_addr) == "Op1Addr.IMM":
            code += str(instruction.imm)
            if str(instruction.ap_update) == "ApUpdate.ADD1":
                code += "; ap++" 
            return code

        elif str(instruction.op1_addr) == "Op1Addr.FP":
            code += "[fp"
        else:
            code += "[ap"

        if instruction.off2 > 0:
            code += "+" + str(instruction.off2)
        elif instruction.off2 < 0:
            code += str(instruction.off2)
        code += "]"

    if str(instruction.ap_update) == "ApUpdate.ADD1":
        code += "; ap++" 
        
    return code


def decode_if(instruction) -> str:
    code = ""
    # If the instruction is just an assignation:
    if instruction.off1 == -1 and instruction.off2 == 1:
        if str(instruction.res) == "Res.OP1":
            return str(instruction.imm)

        if str(instruction.res) == "Res.ADD":
            code += "["

            code += "ap" if str(instruction.op0_register) == "Register.AP" else "fp"

            if instruction.off1 > 0:
                code += "+" + str(instruction.off1)
            elif instruction.off1 < 0:
                code += str(instruction.off1)
            code +=  "] + "
        if str(instruction.res) == "Res.MUL":
            code += "["

            code += "ap" if str(instruction.op0_register) == "Register.AP" else "fp"

            if instruction.off1 > 0:
                code += "+" + str(instruction.off1)
            elif instruction.off1 < 0:
                code += str(instruction.off1)
            code +=  "] * "
        if instruction.imm - ((2**251) + (17 * (2**192)) + 1 ) < 0:
                code = code[:-3] + str(instruction.imm - ((2**251) + (17 * (2**192)) + 1 ))
        else:
            code += str(instruction.imm)
        return code
    elif instruction.imm == None:
        code += "[ap" if str(instruction.op0_register) == "Register.AP" else "[fp"

        if instruction.off0 > 0:
            code += "+" + str(instruction.off0)
        elif instruction.off0 < 0:
            code += str(instruction.off0)

        code += "]"

        code += "+" if str(instruction.res) == "Res.ADD" else "*" if str(instruction.res) == "Res.MUL" else ""

        code += "[ap" if str(instruction.op1_addr) == "Op1Addr.AP" else "[fp"

        if instruction.off2 > 0:
            code += "+" + str(instruction.off2)
        elif instruction.off2 < 0:
            code += str(instruction.off2)

        code += "]"

    else:
        code = "..."
    return code









def main():
    
    print()
    analyze("t.json")
    print()

main()