import re

from starkware.cairo.lang.compiler.encode import *
from starkware.cairo.lang.compiler.instruction import Instruction as CairoInstruction

from utils import format_print, PRIME, field_element_repr

def decode_instruction(encoding: int, imm: Optional[int] = None) -> CairoInstruction:
    """
    Given 1 or 2 integers representing an Instruction, returns the Instruction.
    If imm is given for an Instruction with no immediate, it will be ignored.
    """
    flags, off0_enc, off1_enc, off2_enc = decode_instruction_values(encoding)

    # Get dst_register.
    dst_register = Register.FP if (flags >> DST_REG_BIT) & 1 else Register.AP

    # Get op0_register.
    op0_register = Register.FP if (flags >> OP0_REG_BIT) & 1 else Register.AP

    # Get op1.
    op1_addr = {
        (1, 0, 0): CairoInstruction.Op1Addr.IMM,
        (0, 1, 0): CairoInstruction.Op1Addr.AP,
        (0, 0, 1): CairoInstruction.Op1Addr.FP,
        (0, 0, 0): CairoInstruction.Op1Addr.OP0,
    }[(flags >> OP1_IMM_BIT) & 1, (flags >> OP1_AP_BIT) & 1, (flags >> OP1_FP_BIT) & 1]

    if op1_addr is CairoInstruction.Op1Addr.IMM:
        assert imm is not None, "op1_addr is Op1Addr.IMM, but no immediate given"
    else:
        imm = None

    # Get pc_update.
    pc_update = {
        (1, 0, 0): CairoInstruction.PcUpdate.JUMP,
        (0, 1, 0): CairoInstruction.PcUpdate.JUMP_REL,
        (0, 0, 1): CairoInstruction.PcUpdate.JNZ,
        (0, 0, 0): CairoInstruction.PcUpdate.REGULAR,
    }[(flags >> PC_JUMP_ABS_BIT) & 1, (flags >> PC_JUMP_REL_BIT) & 1, (flags >> PC_JNZ_BIT) & 1]

    # Get res.
    res = {
        (1, 0): CairoInstruction.Res.ADD,
        (0, 1): CairoInstruction.Res.MUL,
        (0, 0): CairoInstruction.Res.UNCONSTRAINED
        if pc_update is CairoInstruction.PcUpdate.JNZ
        else CairoInstruction.Res.OP1,
    }[(flags >> RES_ADD_BIT) & 1, (flags >> RES_MUL_BIT) & 1]

    # JNZ opcode means res must be UNCONSTRAINED.
    if pc_update is CairoInstruction.PcUpdate.JNZ:
        assert res is CairoInstruction.Res.UNCONSTRAINED

    # Get ap_update.
    ap_update = {
        (1, 0): CairoInstruction.ApUpdate.ADD,
        (0, 1): CairoInstruction.ApUpdate.ADD1,
        (0, 0): CairoInstruction.ApUpdate.REGULAR,  # OR ADD2, depending if we have CALL opcode.
    }[(flags >> AP_ADD_BIT) & 1, (flags >> AP_ADD1_BIT) & 1]

    # Get opcode.
    opcode = {
        (1, 0, 0): CairoInstruction.Opcode.CALL,
        (0, 1, 0): CairoInstruction.Opcode.RET,
        (0, 0, 1): CairoInstruction.Opcode.ASSERT_EQ,
        (0, 0, 0): CairoInstruction.Opcode.NOP,
    }[
        (flags >> OPCODE_CALL_BIT) & 1,
        (flags >> OPCODE_RET_BIT) & 1,
        (flags >> OPCODE_ASSERT_EQ_BIT) & 1,
    ]

    # CALL opcode means ap_update must be ADD2.
    if opcode is CairoInstruction.Opcode.CALL:
        assert ap_update is CairoInstruction.ApUpdate.REGULAR, "CALL must have update_ap is ADD2"
        ap_update = CairoInstruction.ApUpdate.ADD2

    # Get fp_update.
    if opcode is CairoInstruction.Opcode.CALL:
        fp_update = CairoInstruction.FpUpdate.AP_PLUS2
    elif opcode is CairoInstruction.Opcode.RET:
        fp_update = CairoInstruction.FpUpdate.DST
    else:
        fp_update = CairoInstruction.FpUpdate.REGULAR

    return CairoInstruction(
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

class Instruction:
    def __init__(self, id, instruction_data):
        self.id = id
        self.offDest = instruction_data.get("off0") if instruction_data.get("off0")[0] == '-' else '+' + instruction_data.get("off0")
        self.offDest = self.offDest if int(self.offDest) != 0 else ""
        self.off1 = instruction_data.get("off1") if instruction_data.get("off1")[0] == '-' else '+' + instruction_data.get("off1")
        self.off1 = self.off1 if int(self.off1) != 0 else ""
        self.off2 = instruction_data.get("off2") if instruction_data.get("off2")[0] == '-' else '+' + instruction_data.get("off2")
        self.off2 = self.off2 if int(self.off2) != 0 else ""
        self.imm = instruction_data.get("imm")
        self.dstRegister = instruction_data.get("dst_register").split("Register.")[1]
        self.op0Register = instruction_data.get("op0_register").split("Register.")[1]
        self.op1Addr = instruction_data.get("op1_addr").split("Op1Addr.")[1]
        self.res = instruction_data.get("res").split("Res.")[1]
        self.pcUpdate = instruction_data.get("pc_update").split("PcUpdate.")[1]
        self.apUpdate = instruction_data.get("ap_update").split("ApUpdate.")[1]
        self.fpUpdate = instruction_data.get("fp_update").split("FpUpdate.")[1]
        self.opcode = instruction_data.get("opcode").split("Opcode.")[1]
        self.call_xref_func_name = None

    def is_call_indirect(self):
        """
        This instruction is an Indirect CALL
        """
        return ("CALL" == self.opcode) and (self.imm == 'None')

    def is_call_direct(self):
        """
        This instruction is a Direct CALL
        """
        return ("CALL" == self.opcode) and (self.imm != 'None')

    def is_return(self):
        """
        This instruction is a RET
        """
        return ("RET" == self.opcode)

    def _handle_assert_eq(self):
        """
        Handle ASSERT_EQ opcode
        """
        OPERATORS = {"ADD" : "+", "MUL" : "*"}

        disass_str = ""
        disass_str += format_print(f"{self.opcode}")
        if ("OP1" in self.res):
            if ("IMM" in self.op1Addr):
                disass_str += format_print(f"[{self.dstRegister}{self.offDest}], {field_element_repr(int(self.imm), PRIME)}")
            elif ("OP0" in self.op1Addr):
                disass_str += format_print(f"[{self.dstRegister}{self.offDest}], [[{self.op0Register}{self.off1}]{self.off2}]")
            else:
                disass_str += format_print(f"[{self.dstRegister}{self.offDest}], [{self.op1Addr}{self.off2}]") 
        else:
            op = OPERATORS[self.res]
            if ("IMM" not in self.op1Addr):
                disass_str += format_print(f"[{self.dstRegister}{self.offDest}], [{self.op0Register}{self.off1}] {op} [{self.op1Addr}{self.off2}]")  
            else:
                disass_str += format_print(f"[{self.dstRegister}{self.offDest}], [{self.op0Register}{self.off1}] {op} {field_element_repr(int(self.imm), PRIME)}")
        return disass_str

    def _handle_nop(self):
        """
        Handle NOP opcode
        """
        disass_str = ""
        if ("REGULAR" not in self.pcUpdate):
            disass_str += format_print(f"{self.pcUpdate}")
            disass_str += format_print(field_element_repr(int(self.imm), PRIME))
        else:
            disass_str += format_print(f"{self.opcode}")
        return disass_str

    def _handle_call(self):
        """
        Handle Direct CALL, Indirect CALL and Relative CALL
        """
        disass_str = ""
        disass_str += format_print(f"{self.opcode}")

        # Direct CALL or Relative CALL
        if self.is_call_direct():
            offset = int(self.id) - int(field_element_repr(int(self.imm), PRIME))
            if (offset < 0):
                offset = int(self.id) + int(field_element_repr(int(self.imm), PRIME))
            # direct CALL to a fonction
            if self.call_xref_func_name != None:
                disass_str += format_print(f"{offset} \t# {self.call_xref_func_name}")
            # relative CALL to a label
            # e.g. call rel (123)
            else:
                offset = int(self.id) + int(field_element_repr(int(self.imm), PRIME))
                disass_str += format_print(f"rel ({offset})")

        # Indirect CALL
        # e.g. call rel [fp + 4]
        elif self.is_call_indirect():
            disass_str += format_print(f"rel [{self.op1Addr}{self.off2}]")
        else:
            raise NotImplementedError

        return disass_str

    def _handle_ret(self):
        """
        Handle the RET opcode
        """
        return format_print(f"{self.opcode}")

    def print(self):
        """
        Print the instruction
        """
        disass_str = ""
        disass_str += format_print(f"\noffset {self.id}:")
        if ("ASSERT_EQ" in self.opcode):
            disass_str += self._handle_assert_eq()

        elif ("NOP" in self.opcode):
            disass_str += self._handle_nop()

        elif ("CALL" in self.opcode):
            disass_str += self._handle_call()

        elif ("RET" in self.opcode):
            disass_str += self._handle_ret()

        else:
            # Should never happen - Unknown opcode
            raise AssertionError

        if ("REGULAR" not in self.apUpdate):
            op = list(filter(None, re.split(r'(\d+)', self.apUpdate)))
            APopcode = op[0]
            APval = op[1] if (len(op) > 1) else int(field_element_repr(int(self.imm), PRIME))
            disass_str += format_print(f"\noffset {self.id}:")
            disass_str += format_print(f"{APopcode}")
            disass_str += format_print(f"AP, {APval}")
        return disass_str
