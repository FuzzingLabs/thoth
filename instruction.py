import re

from utils import format_print, PRIME, field_element_repr

class Instruction:
    def __init__(self, inst_id, instruction_data):
        self.id = inst_id
        self.instruction_data = instruction_data
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

    def dump(self):
        print(self.instruction_data)

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
        if "OP1" in self.res:
            if "IMM" in self.op1Addr:
                disass_str += format_print(f"[{self.dstRegister}{self.offDest}], {field_element_repr(int(self.imm), PRIME)}")
            elif "OP0" in self.op1Addr:
                disass_str += format_print(f"[{self.dstRegister}{self.offDest}], [[{self.op0Register}{self.off1}]{self.off2}]")
            else:
                disass_str += format_print(f"[{self.dstRegister}{self.offDest}], [{self.op1Addr}{self.off2}]")
        else:
            op = OPERATORS[self.res]
            if "IMM" not in self.op1Addr:
                disass_str += format_print(f"[{self.dstRegister}{self.offDest}], [{self.op0Register}{self.off1}] {op} [{self.op1Addr}{self.off2}]")
            else:
                disass_str += format_print(f"[{self.dstRegister}{self.offDest}], [{self.op0Register}{self.off1}] {op} {field_element_repr(int(self.imm), PRIME)}")
        return disass_str

    def _handle_nop(self):
        """
        Handle NOP opcode
        """
        disass_str = ""
        if "REGULAR" not in self.pcUpdate:
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
            if offset < 0:
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
        if "ASSERT_EQ" in self.opcode:
            disass_str += self._handle_assert_eq()

        elif "NOP" in self.opcode:
            disass_str += self._handle_nop()

        elif "CALL" in self.opcode:
            disass_str += self._handle_call()

        elif "RET" in self.opcode:
            disass_str += self._handle_ret()

        else:
            # Should never happen - Unknown opcode
            raise AssertionError

        if "REGULAR" not in self.apUpdate:
            op = list(filter(None, re.split(r'(\d+)', self.apUpdate)))
            APopcode = op[0]
            APval = op[1] if (len(op) > 1) else int(field_element_repr(int(self.imm), PRIME))
            disass_str += format_print(f"\noffset {self.id}:")
            disass_str += format_print(f"{APopcode}")
            disass_str += format_print(f"AP, {APval}")
        return disass_str
