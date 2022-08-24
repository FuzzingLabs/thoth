import dis
import re
from thoth import utils

class Decompiler:
    """
    Decompiler class

    decompile bytecodes
    """

    def __init__(self):
        self.tab = 1
        self.end = 0

    def _handle_assert_eq_decomp(self, instruction):
        """Handle the ASSERT_EQ opcode

        Returns:
            String: The formated ASSERT_EQ instruction
        """
        OPERATORS = {"ADD": "+", "MUL": "*"}

        disass_str = ""
        if "OP1" in instruction.res:
            if "IMM" in instruction.op1Addr:
                disass_str += self.print_instruction_decomp(
                    f"[{instruction.dstRegister}{instruction.offDest}] = {utils.field_element_repr(int(instruction.imm), instruction.prime)}"
                )
            elif "OP0" in instruction.op1Addr:
                disass_str += self.print_instruction_decomp(
                    f"[{instruction.dstRegister}{instruction.offDest}] = [[{instruction.op0Register}{instruction.off1}]{instruction.off2}]"
                )
            else:
                disass_str += self.print_instruction_decomp(
                    f"[{instruction.dstRegister}{instruction.offDest}] = [{instruction.op1Addr}{instruction.off2}]"
                )
        else:
            op = OPERATORS[instruction.res]
            if "IMM" not in instruction.op1Addr:
                disass_str += self.print_instruction_decomp(
                    f"[{instruction.dstRegister}{instruction.offDest}] =  [{instruction.op0Register}{instruction.off1}] {op} [{instruction.op1Addr}{instruction.off2}]"
                )
            else:
                disass_str += self.print_instruction_decomp(
                    f"[{instruction.dstRegister}{instruction.offDest}] = [{instruction.op0Register}{instruction.off1}] {op} {utils.field_element_repr(int(instruction.imm), instruction.prime)}"
                )
        return disass_str

    def _handle_nop_decomp(self, instruction):
        """Handle the NOP opcode

        Returns:
            String: The formated NOP instruction
        """
        disass_str = ""
        if "REGULAR" not in instruction.pcUpdate:
            if (instruction.pcUpdate == "JNZ"):
                disass_str += self.print_instruction_decomp("if [AP] == 0:")
                self.tab+=1
            elif (instruction.pcUpdate == "JUMP_REL"):
                self.tab -=1
                disass_str += self.print_instruction_decomp("else:")
                self.tab+=1
                self.end = int(utils.field_element_repr(int(instruction.imm), instruction.prime)) - 1
        return disass_str

    def _handle_call_decomp(self, instruction):
        """Handle the CALL opcode

        Returns:
            String: The formated CALL instruction
        """
        # Direct CALL or Relative CALL
        disass_str = ""
        if instruction.is_call_direct():
            offset = int(instruction.id) + int(utils.field_element_repr(int(instruction.imm), instruction.prime))
            # direct CALL to a fonction
            if instruction.call_xref_func_name is not None:
                call_name = instruction.call_xref_func_name.split(".")
                disass_str += self.print_instruction_decomp(
                    f"{call_name[-1]}()"
               )
            # relative CALL to a label
            # e.g. call rel (123)
            else:
                disass_str += self.print_instruction_decomp(f"rel ({offset})", color=utils.color.BEIGE)
                if str(offset) in instruction.labels:
                    disass_str += self.print_instruction_decomp(
                        f"# {instruction.labels[str(offset)]}", color=utils.color.CYAN
                    )
        # Indirect CALL
        # e.g. call rel [fp + 4]
        elif instruction.is_call_indirect():
            disass_str += self.print_instruction_decomp(
                f"rel [{instruction.op1Addr}{instruction.off2}]", color=utils.color.BEIGE
            )
        else:
            raise NotImplementedError

        return disass_str

    def _handle_ret_decomp(self, instruction):
        """Handle the RET opcode

        Returns:
            String: The formated RET instruction
        """
        disass_str = ""
        disass_str += self.print_instruction_decomp("ret", end="\n")
        self.tab = 0
        disass_str += self.print_instruction_decomp("end")
        return disass_str

    def print_build_code(self, instruction):
        """Read the instruction and print each element of it

        Raises:
            AssertionError: Should never happen - Unknown opcode

        Returns:
            String: String containing the instruction line with the offset ...
        """
        disass_str = ""
        if instruction.id in instruction.labels:
            disass_str += self.print_instruction_decomp(
                f"\nLABEL : {instruction.labels[instruction.id]}", color=utils.color.GREEN
            )
        if "ASSERT_EQ" in instruction.opcode:
            disass_str += self._handle_assert_eq_decomp(instruction)

        elif "NOP" in instruction.opcode:
            disass_str += self._handle_nop_decomp(instruction)
        elif "CALL" in instruction.opcode:
            disass_str += self._handle_call_decomp(instruction)

        elif "RET" in instruction.opcode:
            disass_str += self._handle_ret_decomp(instruction)

        else:
            raise AssertionError

        if "REGULAR" not in instruction.apUpdate:
            disass_str += "; "
            disass_str += self.print_instruction_decomp(f"ap++", tab=1)

        if instruction.hint:
            disass_str += self.print_instruction_decomp(f" # {instruction.hint}", color=utils.color.BEIGE)

        return disass_str

    def print_instruction_decomp(self, data, color="", end="", tab=None):
        """format the instruction

        Args:
            data (String): Data to print
            color (str, optional): Color to use. Defaults to "".
            end (str, optional): End of the string. Defaults to "".

        Returns:
            String: The formated Instruction
        """
        tabulation = "    " * self.tab
        if (tab != None):
            tabulation = "    " * tab
        return color + tabulation + data + utils.color.ENDC + end

    def decompile_code(self, functions):
        for function in functions:
            function.generate_cfg()
        for function in functions:
            print(function.get_prototype())
            self.tab+=1
            if (function.cfg.basicblocks != []):
                for block in function.cfg.basicblocks:
                    for instruction in block.instructions:
                        if (self.end != 0):
                            self.end-=1
                            if (self.end == 1):
                                self.tab -=1
                                print(self.print_instruction_decomp("end"))
                        instruction = self.print_build_code(instruction)
                        print(instruction)
                    