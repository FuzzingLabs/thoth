import re

from starkware.cairo.lang.compiler.encode import *
from starkware.cairo.lang.compiler.instruction import Instruction as CairoInstruction

from utils import format_print, OPERATORS, PRIME

def decodeInstruction(encoding: int, imm: Optional[int] = None) -> CairoInstruction:
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
    def __init__(self, instruction_data, id):
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
        self.nextInstruction = None

    def _handle_assert_eq(self):
        format_print(f"{self.opcode}", end="")
        if ("OP1" in self.res):
            if ("IMM" in self.op1Addr):
                format_print(f"[{self.dstRegister}{self.offDest}], {self.imm}")
            elif ("OP0" in self.op1Addr):
                format_print(f"[{self.dstRegister}{self.offDest}], [[{self.op0Register}{self.off1}]{self.off2}]")
            else:
                format_print(f"[{self.dstRegister}{self.offDest}], [{self.op1Addr}{self.off2}]") 
        else:
            op = OPERATORS[self.res]
            if ("IMM" not in self.op1Addr):
                format_print(f"[{self.dstRegister}{self.offDest}], [{self.op0Register}{self.off1}] {op} [{self.op1Addr}{self.off2}]")  
            else:
                format_print(f"[{self.dstRegister}{self.offDest}], [{self.op0Register}{self.off1}] {op} {self.imm}")

    def _handle_nop(self):
        if ("REGULAR" not in self.pcUpdate):
            ##TODO JNZ OFFSET ?!
            format_print(f"{self.pcUpdate}", end="")
            format_print(self.imm)
        else:
            format_print(f"{self.opcode}")
        #newOffset = int(self.id) + int(self.imm)
        #format_print(f"{newOffset}")

    def _handle_call(self):
        format_print(f"{self.opcode}", end="")
        offset = int(self.id) - (PRIME - int(self.imm))
        if (offset < 0):
            offset = int(self.id) + int(self.imm)
        format_print(f"{offset}")
        #format_print(f"{offset}=>{##need to get the function name}")

    def _handle_ret(self):
        format_print(f"{self.opcode}")

    def print(self):
        format_print(f"offset {self.id}:", end="")
        if ("ASSERT_EQ" in self.opcode):
            self._handle_assert_eq()

        elif ("NOP" in self.opcode):
            self._handle_nop()

        elif ("CALL" in self.opcode):
            self._handle_call()

        elif ("RET" in self.opcode):
            self._handle_ret()

        else:
            format_print("--TODO--")
            raise NotImplementedError

        if ("REGULAR" not in self.apUpdate):
            op = list(filter(None, re.split(r'(\d+)', self.apUpdate)))
            APopcode = op[0]
            APval = op[1] if (len(op) > 1) else self.imm
            format_print(f"offset {self.id}:", end="")
            format_print(f"{APopcode}", end="")
            format_print(f"AP, {APval}")
