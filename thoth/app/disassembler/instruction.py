import re
from thoth.app import utils
from thoth.app.utils import field_element_repr, value_to_string


class Instruction:
    def __init__(
        self,
        instruction_id: str,
        instruction_data: str,
        prime: int,
        labels: dict,
    ) -> None:
        """Create the instruction object

        Args:
            instruction_id (String): Offset of the instruction
            instruction_data (Dictionary): Dictionnary containing the instruction data
            prime (Int): The prime number
            labels (Dictionary): Dictionary containing the labels
        """
        self.id = instruction_id
        self.instruction_data = instruction_data
        self.prime = prime
        self.labels = labels
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

    def _find_call_offset(self) -> int:
        """Find the offset of the call

        Returns:
            Int: The offset of the call
        """
        if self.is_call_direct():
            if self.imm != None:
                return int(self.id) + int(field_element_repr(int(self.imm), self.prime))
        return 0

    def is_call_indirect(self) -> bool:
        """Check if the instruction is a CALL INDIRECT

        Returns:
            Boolean: True if the opcode is a CALL INDIRECT
        """
        return ("CALL" == self.opcode) and (self.imm == "None")

    def is_call_direct(self) -> bool:
        """Check if the instruction is a CALL DIRECT

        Returns:
            Boolean: True if the opcode is a CALL DIRECT
        """
        return ("CALL" == self.opcode) and (self.imm != "None")

    def is_call_abs(self) -> bool:
        """Check if the instruction is a absolute CALL

        Returns:
            Boolean: True
        """
        return ("CALL" == self.opcode) and (self.pcUpdate == "JUMP")

    def is_return(self) -> bool:
        """Check if the instruction is a RET

        Returns:
            Boolean: True if the opcode is a RET
        """
        return "RET" == self.opcode

    def _handle_assert_eq(self) -> str:
        """Handle the ASSERT_EQ opcode

        Returns:
            String: The formated ASSERT_EQ instruction
        """
        assembly = ""

        OPERATORS = {"ADD": "+", "MUL": "*"}

        assembly += self.print_instruction(f"{self.opcode}", color=utils.color.GREEN)
        if "OP1" in self.res:
            if "IMM" in self.op1Addr:
                assembly += self.print_instruction(
                    f"[{self.dstRegister}{self.offDest}], {field_element_repr(int(self.imm), self.prime)}"
                )
                value = value_to_string(int(self.imm), self.prime)
                if value != "":
                    assembly += self.print_instruction(
                        f"# {value_to_string(int(self.imm), self.prime)}",
                        color=utils.color.CYAN,
                    )
            elif "OP0" in self.op1Addr:
                assembly += self.print_instruction(
                    f"[{self.dstRegister}{self.offDest}], [[{self.op0Register}{self.off1}]{self.off2}]"
                )
            else:
                assembly += self.print_instruction(
                    f"[{self.dstRegister}{self.offDest}], [{self.op1Addr}{self.off2}]"
                )
        else:
            op = OPERATORS[self.res]
            if "IMM" not in self.op1Addr:
                assembly += self.print_instruction(
                    f"[{self.dstRegister}{self.offDest}], [{self.op0Register}{self.off1}] {op} [{self.op1Addr}{self.off2}]"
                )
            else:
                assembly += self.print_instruction(
                    f"[{self.dstRegister}{self.offDest}], [{self.op0Register}{self.off1}] {op} {field_element_repr(int(self.imm), self.prime)}"
                )
        return assembly

    def _handle_nop(self) -> str:
        """Handle the NOP opcode

        Returns:
            String: The formated NOP instruction
        """
        assembly = ""

        if "REGULAR" not in self.pcUpdate and self.imm != "None":
            assembly += self.print_instruction(f"{self.pcUpdate}", color=utils.color.RED)
            assembly += self.print_instruction(
                field_element_repr(int(self.imm), self.prime), utils.color.BLUE
            )
            jump_to = int(field_element_repr(int(self.imm), self.prime)) + int(self.id)
            if str(jump_to) in self.labels:
                assembly += self.print_instruction(
                    f"# JMP {self.labels[str(jump_to)]}",
                    color=utils.color.CYAN,
                )
            else:
                assembly += self.print_instruction(
                    f"# JMP {jump_to}",
                    color=utils.color.CYAN,
                )
        else:
            assembly += self.print_instruction(f"{self.opcode}", color=utils.color.RED)
        return assembly

    def _handle_call(self):
        """Handle the CALL opcode

        Returns:
            String: The formated CALL instruction
        """
        assembly = "" + self.print_instruction(f"{self.opcode}", color=utils.color.RED)
        call_type = "abs" if self.is_call_abs() else "rel"

        # Direct CALL or Relative CALL
        if self.is_call_direct():
            offset = int(self.id) + int(field_element_repr(int(self.imm), self.prime))
            # direct CALL to a fonction
            if self.call_xref_func_name is not None:
                assembly += self.print_instruction(f"{offset}", color=utils.color.CYAN)
                assembly += self.print_instruction(
                    f"# {self.call_xref_func_name}", color=utils.color.CYAN
                )
            # relative CALL to a label
            # e.g. call rel (123)
            else:
                assembly += self.print_instruction(
                    f"{call_type} ({offset})", color=utils.color.BEIGE
                )
                if str(offset) in self.labels:
                    assembly += self.print_instruction(
                        f"# {self.labels[str(offset)]}", color=utils.color.CYAN
                    )
        # Indirect CALL
        # e.g. call rel [fp + 4]
        elif self.is_call_indirect():
            assembly += self.print_instruction(
                f"{call_type} [{self.op1Addr}{self.off2}]",
                color=utils.color.BEIGE,
            )
        else:
            raise NotImplementedError

        return assembly

    def _handle_ret(self) -> str:
        """Handle the RET opcode

        Returns:
            String: The formated RET instruction
        """
        return self.print_instruction(f"{self.opcode}", color=utils.color.RED)

    def print(self) -> str:
        """Read the instruction and print each element of it

        Raises:
            AssertionError: Should never happen - Unknown opcode

        Returns:
            String: String containing the instruction line with the offset ...
        """
        assembly = ""
        if self.id in self.labels:
            assembly += self.print_instruction(
                f"\nLABEL : {self.labels[self.id]}", color=utils.color.GREEN
            )
        assembly += self.print_instruction(f"\noffset {self.id}:", color=utils.color.HEADER)

        if "ASSERT_EQ" in self.opcode:
            assembly += self._handle_assert_eq()
            if "REGULAR" not in self.apUpdate:
                op = list(filter(None, re.split(r"(\d+)", self.apUpdate)))
                APopcode = op[0]
                APval = (
                    op[1] if (len(op) > 1) else int(field_element_repr(int(self.imm), self.prime))
                )
                assembly += self.print_instruction(f"\noffset {self.id}:", color=utils.color.HEADER)
                assembly += self.print_instruction(f"{APopcode}", color=utils.color.YELLOW)
                assembly += self.print_instruction(f"AP, {APval}")

        elif "NOP" in self.opcode:
            assembly += self._handle_nop()

        elif "CALL" in self.opcode:
            assembly += self._handle_call()

        elif "RET" in self.opcode:
            assembly += self._handle_ret()

        else:
            raise AssertionError

        if self.hint:
            assembly += self.print_instruction(f" # {self.hint}", color=utils.color.BEIGE)
        return assembly

    def print_instruction(self, data: str, color: str = "", end: str = "") -> str:
        """format the instruction

        Args:
            data (String): Data to print
            color (str, optional): Color to use. Defaults to "".
            end (str, optional): End of the string. Defaults to "".

        Returns:
            String: The formated Instruction
        """
        spaces = " " * 20
        return color + data + utils.color.ENDC + spaces[len(data) :] + end
