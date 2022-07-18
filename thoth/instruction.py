#!/usr/bin/env python3

import re
from .utils import field_element_repr
import thoth.utils as utils


class Instruction:
    def __init__(self, inst_id, instruction_data, prime):
        self.id = inst_id
        self.instruction_data = instruction_data
        self.prime = prime
        self.offDest = (
            instruction_data.get("off0")
            if instruction_data.get("off0")[0] == "-"
            else "+" + instruction_data.get("off0")
        )
        self.offDest = self.offDest if int(self.offDest) != 0 else ""
        self.off1 = (
            instruction_data.get("off1")
            if instruction_data.get("off1")[0] == "-"
            else "+" + instruction_data.get("off1")
        )
        self.off1 = self.off1 if int(self.off1) != 0 else ""
        self.off2 = (
            instruction_data.get("off2")
            if instruction_data.get("off2")[0] == "-"
            else "+" + instruction_data.get("off2")
        )
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
        self.ref = None
        self.hint = None
        # Specific values
        self.call_xref_func_name = None
        self.call_offset = self._find_call_offset()

    def _find_call_offset(self):
        if self.is_call_direct():
            return int(self.id) + int(field_element_repr(int(self.imm), self.prime))
        else:
            None

    def dump(self):
        print(self.instruction_data)

    def is_call_indirect(self):
        """
        This instruction is an Indirect CALL
        """
        return ("CALL" == self.opcode) and (self.imm == "None")

    def is_call_direct(self):
        """
        This instruction is a Direct CALL
        """
        return ("CALL" == self.opcode) and (self.imm != "None")

    def is_return(self):
        """
        This instruction is a RET
        """
        return "RET" == self.opcode

    def _handle_assert_eq(self):
        """
        Handle ASSERT_EQ opcode
        """
        OPERATORS = {"ADD": "+", "MUL": "*"}

        disass_str = ""
        disass_str += self.print_instruction(f"{self.opcode}", color=utils.color.GREEN)
        if "OP1" in self.res:
            if "IMM" in self.op1Addr:
                disass_str += self.print_instruction(
                    f"[{self.dstRegister}{self.offDest}], {field_element_repr(int(self.imm), self.prime)}"
                )
            elif "OP0" in self.op1Addr:
                disass_str += self.print_instruction(
                    f"[{self.dstRegister}{self.offDest}], [[{self.op0Register}{self.off1}]{self.off2}]"
                )
            else:
                disass_str += self.print_instruction(
                    f"[{self.dstRegister}{self.offDest}], [{self.op1Addr}{self.off2}]"
                )
        else:
            op = OPERATORS[self.res]
            if "IMM" not in self.op1Addr:
                disass_str += self.print_instruction(
                    f"[{self.dstRegister}{self.offDest}], [{self.op0Register}{self.off1}] {op} [{self.op1Addr}{self.off2}]"
                )
            else:
                disass_str += self.print_instruction(
                    f"[{self.dstRegister}{self.offDest}], [{self.op0Register}{self.off1}] {op} {field_element_repr(int(self.imm), self.prime)}"
                )
        return disass_str

    def _handle_nop(self):
        """
        Handle NOP opcode
        """
        disass_str = ""
        if "REGULAR" not in self.pcUpdate:
            disass_str += self.print_instruction(
                f"{self.pcUpdate}", color=utils.color.RED
            )
            disass_str += self.print_instruction(
                field_element_repr(int(self.imm), self.prime), utils.color.BLUE
            )
        else:
            disass_str += self.print_instruction(
                f"{self.opcode}", color=utils.color.RED
            )
        return disass_str

    def _handle_call(self):
        """
        Handle Direct CALL, Indirect CALL and Relative CALL
        """
        disass_str = ""
        disass_str += self.print_instruction(f"{self.opcode}", color=utils.color.RED)

        # Direct CALL or Relative CALL
        if self.is_call_direct():
            offset = int(self.id) + int(field_element_repr(int(self.imm), self.prime))
            # direct CALL to a fonction
            if self.call_xref_func_name is not None:
                disass_str += self.print_instruction(
                    f"{offset}",
                )
                disass_str += self.print_instruction(
                    f"# {self.call_xref_func_name}", color=utils.color.BEIGE
                )
            # relative CALL to a label
            # e.g. call rel (123)
            else:
                disass_str += self.print_instruction(
                    f"rel ({offset})", color=utils.color.BLUE
                )

        # Indirect CALL
        # e.g. call rel [fp + 4]
        elif self.is_call_indirect():
            disass_str += self.print_instruction(
                f"rel [{self.op1Addr}{self.off2}]", color=utils.color.BLUE
            )
        else:
            raise NotImplementedError

        return disass_str

    def _handle_ret(self):
        """
        Handle the RET opcode
        """
        return self.print_instruction(f"{self.opcode}", color=utils.color.RED)

    def print(self):
        """
        Print the instruction
        """
        disass_str = ""
        disass_str += self.print_instruction(
            f"\noffset {self.id}:", color=utils.color.HEADER
        )
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
            op = list(filter(None, re.split(r"(\d+)", self.apUpdate)))
            APopcode = op[0]
            APval = (
                op[1]
                if (len(op) > 1)
                else int(field_element_repr(int(self.imm), self.prime))
            )
            disass_str += self.print_instruction(
                f"\noffset {self.id}:", color=utils.color.HEADER
            )
            disass_str += self.print_instruction(
                f"{APopcode}", color=utils.color.YELLOW
            )
            disass_str += self.print_instruction(f"AP, {APval}")

        if self.ref:
            disass_str += self.print_instruction(
                f"# {self.ref}", color=utils.color.BEIGE
            )
        if self.hint:
            disass_str += self.print_instruction(
                f"# {self.hint}", color=utils.color.BEIGE
            )

        return disass_str

    def print_instruction(self, data, color="", end=""):
        """
        Format the print
        """
        spaces = " " * 20
        return color + data + utils.color.ENDC + spaces[len(data) :] + end
