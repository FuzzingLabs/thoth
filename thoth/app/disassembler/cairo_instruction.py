# https://github.com/starkware-libs/cairo-lang/blob/4e233516f52477ad158bc81a86ec2760471c1b65/src/starkware/cairo/lang/compiler/instruction.py

import dataclasses
from enum import Enum, auto
from typing import Optional, Tuple

OFFSET_BITS = 16
N_FLAGS = 15


class Register(Enum):
    AP = 0
    FP = auto()


class BytecodeElement:
    @property
    def size(self):
        raise NotImplementedError


@dataclasses.dataclass
class BytecodeData(BytecodeElement):
    data: int

    @property
    def size(self):
        return 1


@dataclasses.dataclass
class Instruction(BytecodeElement):
    # Offsets. In the range [-2**15, 2*15) = [-2**(OFFSET_BITS-1), 2**(OFFSET_BITS-1)).
    off0: int
    off1: int
    off2: int

    # Immediate.
    imm: Optional[int]

    # Flags for operands.
    dst_register: Register
    op0_register: Register

    class Op1Addr(Enum):
        # op1 = [pc + 1].
        IMM = 0
        # op1 = [ap + off2].
        AP = auto()
        # op1 = [fp + off2].
        FP = auto()
        # op1 = [op0].
        OP0 = auto()

    op1_addr: Op1Addr

    class Res(Enum):
        # res = operand_1.
        OP1 = 0
        # res = operand_0 + operand_1.
        ADD = auto()
        # res = operand_0 * operand_1.
        MUL = auto()
        # res is not constrained.
        UNCONSTRAINED = auto()

    res: Res

    # Flags for register update.
    class PcUpdate(Enum):
        # Next pc: pc + op_size.
        REGULAR = 0
        # Next pc: res (jmp abs).
        JUMP = auto()
        # Next pc: pc + res (jmp rel).
        JUMP_REL = auto()
        # Next pc: jnz_addr (jnz), where jnz_addr is a complex expression, representing the jnz
        # logic.
        JNZ = auto()

    pc_update: PcUpdate

    class ApUpdate(Enum):
        # Next ap: ap.
        REGULAR = 0
        # Next ap: ap + [pc + 1].
        ADD = auto()
        # Next ap: ap + 1.
        ADD1 = auto()
        # Next ap: ap + 2.
        ADD2 = auto()

    ap_update: ApUpdate

    class FpUpdate(Enum):
        # Next fp: fp.
        REGULAR = 0
        # Next fp: ap + 2.
        AP_PLUS2 = auto()
        # Next fp: operand_dst.
        DST = auto()

    fp_update: FpUpdate

    # Flags for opcodes.
    class Opcode(Enum):
        NOP = 0
        ASSERT_EQ = auto()
        CALL = auto()
        RET = auto()

    opcode: Opcode

    @property
    def size(self) -> int:
        return 2 if self.imm is not None else 1


def decode_instruction_values(encoded_instruction: str) -> Tuple:
    """Returns a tuple (flags, off0, off1, off2) according to the given encoded instruction.


    Args:
        encoded_instruction (String): The encoded instruction

    Returns:
        Tuple: Decoded instruction
    """
    # assert 0 <= encoded_instruction < 2 ** (3 * OFFSET_BITS + N_FLAGS), "Unsupported instruction."
    off0 = encoded_instruction & (2**OFFSET_BITS - 1)
    off1 = (encoded_instruction >> OFFSET_BITS) & (2**OFFSET_BITS - 1)
    off2 = (encoded_instruction >> (2 * OFFSET_BITS)) & (2**OFFSET_BITS - 1)
    flags_val = encoded_instruction >> (3 * OFFSET_BITS)
    return flags_val, off0, off1, off2


DST_REG_BIT = 0
OP0_REG_BIT = 1
OP1_IMM_BIT = 2
OP1_FP_BIT = 3
OP1_AP_BIT = 4
RES_ADD_BIT = 5
RES_MUL_BIT = 6
PC_JUMP_ABS_BIT = 7
PC_JUMP_REL_BIT = 8
PC_JNZ_BIT = 9
AP_ADD_BIT = 10
AP_ADD1_BIT = 11
OPCODE_CALL_BIT = 12
OPCODE_RET_BIT = 13
OPCODE_ASSERT_EQ_BIT = 14
# RESERVED_BIT = 15.

# https://github.com/starkware-libs/cairo-lang/blob/4e233516f52477ad158bc81a86ec2760471c1b65/src/starkware/cairo/lang/compiler/encode.py#L131
def decode_instruction(encoding: int, imm: Optional[int] = None) -> Instruction:
    """Given 1 or 2 integers representing an instruction, returns the Instruction.
    If imm is given for an instruction with no immediate, it will be ignored.

    Args:
        encoding (int): The bytecode
        imm (Optional[int], optional): The imm value. Defaults to None.

    Returns:
        Instruction: Decoded instruction object
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
    }[
        (flags >> OP1_IMM_BIT) & 1,
        (flags >> OP1_AP_BIT) & 1,
        (flags >> OP1_FP_BIT) & 1,
    ]

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
    }[
        (flags >> PC_JUMP_ABS_BIT) & 1,
        (flags >> PC_JUMP_REL_BIT) & 1,
        (flags >> PC_JNZ_BIT) & 1,
    ]

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
        (
            0,
            0,
        ): Instruction.ApUpdate.REGULAR,  # OR ADD2, depending if we have CALL opcode.
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
