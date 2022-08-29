import re
from thoth import utils


class Decompiler:
    """
    Decompiler class

    decompile bytecodes
    """

    def __init__(self, functions):
        self.tab = 1
        self.end = 0
        self.ap = []
        self.ifcount = 0
        self.functions = functions

    def _handle_assert_eq_decomp(self, instruction):
        """Handle the ASSERT_EQ opcode

        Returns:
            String: The formated ASSERT_EQ instruction
        """
        OPERATORS = {"ADD": "+", "MUL": "*"}

        decomp_str = ""
        if "OP1" in instruction.res:
            if "IMM" in instruction.op1Addr:
                decomp_str += self.print_instruction_decomp(
                    f"[{instruction.dstRegister}{instruction.offDest}] = {utils.field_element_repr(int(instruction.imm), instruction.prime)}"
                )
            elif "OP0" in instruction.op1Addr:
                decomp_str += self.print_instruction_decomp(
                    f"[{instruction.dstRegister}{instruction.offDest}] = [[{instruction.op0Register}{instruction.off1}]{instruction.off2}]"
                )
            else:
                decomp_str += self.print_instruction_decomp(
                    f"[{instruction.dstRegister}{instruction.offDest}] = [{instruction.op1Addr}{instruction.off2}]"
                )
        else:
            op = OPERATORS[instruction.res]
            if "IMM" not in instruction.op1Addr:
                decomp_str += self.print_instruction_decomp(
                    f"[{instruction.dstRegister}{instruction.offDest}] =  [{instruction.op0Register}{instruction.off1}] {op} [{instruction.op1Addr}{instruction.off2}]"
                )
            else:
                decomp_str += self.print_instruction_decomp(
                    f"[{instruction.dstRegister}{instruction.offDest}] = [{instruction.op0Register}{instruction.off1}] {op} {utils.field_element_repr(int(instruction.imm), instruction.prime)}"
                )
        return decomp_str

    def _handle_nop_decomp(self, instruction):
        """Handle the NOP opcode

        Returns:
            String: The formated NOP instruction
        """
        decomp_str = ""
        if "REGULAR" not in instruction.pcUpdate:
            if instruction.pcUpdate == "JNZ":
                decomp_str += self.print_instruction_decomp(f"if [AP{instruction.offDest}] == 0:")
                self.tab += 1
                self.ifcount += 1
            elif instruction.pcUpdate == "JUMP_REL":
                if self.ifcount != 0:
                    self.tab -= 1
                    decomp_str += self.print_instruction_decomp("else:")
                    self.tab += 1
                    self.end = (
                        int(
                            utils.field_element_repr(
                                int(instruction.imm), instruction.prime
                            )
                        )
                        - 1
                    )
                    self.ifcount -= 1
                else:
                    decomp_str += self.print_instruction_decomp(
                        f"jmp rel {instruction.imm}"
                    )
        return decomp_str

    def _handle_call_decomp(self, instruction):
        """Handle the CALL opcode

        Returns:
            String: The formated CALL instruction
        """
        # Direct CALL or Relative CALL
        decomp_str = ""
        call_type = "call abs" if instruction.is_call_abs() else "call rel"
        if instruction.is_call_direct():
            offset = int(
                utils.field_element_repr(
                    int(instruction.imm), instruction.prime
                )
            )
            # direct CALL to a fonction
            if instruction.call_xref_func_name is not None:
                call_name = instruction.call_xref_func_name.split(".")
                args = 0
                for function in self.functions:
                    if function.name == instruction.call_xref_func_name:
                        if function.args != None:
                            args += len(function.args)
                        if function.implicitargs != None:
                            args += len(function.implicitargs)
                args_str = ""
                while args != 0:
                    args_str += f"[ap-{args}]"
                    if args != 1:
                        args_str += ", "
                    args -= 1
                decomp_str += self.print_instruction_decomp(
                    f"{call_name[-1]}({args_str})"
                )
            # CALL to a label
            # e.g. call rel (123)
            else:
                decomp_str += self.print_instruction_decomp(
                    f"{call_type} ({offset})"
                )
                if str(offset) in instruction.labels:
                    decomp_str += self.print_instruction_decomp(
                        f"# {instruction.labels[str(offset)]}"
                    )
        # CALL
        # e.g. call rel [fp + 4]
        elif instruction.is_call_indirect():
            decomp_str += self.print_instruction_decomp(
                f"{call_type} [{instruction.op1Addr}{instruction.off2}]"
            )
        else:
            raise NotImplementedError

        return decomp_str

    def _handle_ret_decomp(self, instruction, last=False):
        """Handle the RET opcode

        Returns:
            String: The formated RET instruction
        """
        decomp_str = ""
        decomp_str += self.print_instruction_decomp("ret", end="\n")
        if last:
            self.tab = 0
            decomp_str += self.print_instruction_decomp("end")
        return decomp_str

    def _handle_hint_decomp(self, instruction, last=False):
        """Handle the hint

        Returns:
            String: The formated hint
        """
        hints = instruction.hint.split("\n")
        decomp_str = ""
        decomp_str += self.print_instruction_decomp("%{ ", end="\n")
        self.tab += 1
        for hint in hints:
            decomp_str += self.print_instruction_decomp(hint, end="\n")
        self.tab -= 1
        decomp_str += self.print_instruction_decomp("%} ", end="\n")
        return decomp_str

    def print_build_code(self, instruction, last=False):
        """Read the instruction and print each element of it

        Raises:
            AssertionError: Should never happen - Unknown opcode

        Returns:
            String: String containing the instruction line with the offset ...
        """
        decomp_str = ""
        if instruction.id in instruction.labels:
            decomp_str += self.print_instruction_decomp(
                f"\nLABEL : {instruction.labels[instruction.id]}",
                color=utils.color.GREEN,
            )
        if instruction.hint:
            decomp_str += self._handle_hint_decomp(instruction)

        if "ASSERT_EQ" in instruction.opcode:
            decomp_str += self._handle_assert_eq_decomp(instruction)
            if "REGULAR" not in instruction.apUpdate:
                decomp_str += ";"
                op = list(
                    filter(None, re.split(r"(\d+)", instruction.apUpdate))
                )
                APval = (
                    op[1]
                    if (len(op) > 1)
                    else int(
                        utils.field_element_repr(
                            int(instruction.imm), instruction.prime
                        )
                    )
                )
                for i in range(int(APval)):
                    decomp_str += self.print_instruction_decomp(
                        f"ap ++", tab=self.tab
                    )
                    if i != int(APval) - 1:
                        decomp_str += "\n"
        elif "NOP" in instruction.opcode:
            decomp_str += self._handle_nop_decomp(instruction)
        elif "CALL" in instruction.opcode:
            decomp_str += self._handle_call_decomp(instruction)
        elif "RET" in instruction.opcode:
            decomp_str += self._handle_ret_decomp(instruction, last=last)
        else:
            raise AssertionError
        return decomp_str

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
        if tab != None:
            tabulation = "    " * tab
        return color + tabulation + data + utils.color.ENDC + end

    def decompile_code(self):
        for function in self.functions:
            if function.is_import is False:
                function.generate_cfg()
                print(function.get_prototype())
                self.tab += 1
                if function.cfg.basicblocks != []:
                    for block in function.cfg.basicblocks:
                        for count, instruction in enumerate(
                            block.instructions, start=1
                        ):
                            if self.end != 0:
                                self.end -= 1
                                if self.end == 1:
                                    self.tab -= 1
                                    print(self.print_instruction_decomp("end"))
                            instruction = self.print_build_code(
                                instruction,
                                last=(count == len(block.instructions)),
                            )
                            print(instruction)