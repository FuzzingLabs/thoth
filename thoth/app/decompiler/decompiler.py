import re
from typing import List
from thoth.app import utils
from thoth.app.disassembler.function import Function
from thoth.app.disassembler.instruction import Instruction
from thoth.app.decompiler.ssa import SSA

class Decompiler:
    """
    Decompiler class

    decompile bytecodes
    """

    def __init__(self, functions: List[Function]) -> None:
        self.tab_count = 1
        self.end_else = []
        self.ifcount = 0
        self.end_if = None
        self.functions = functions
        self.decompiled_function = None
        self.return_values = None
        # Static single assignment
        self.ssa = SSA()

    def _handle_assert_eq_decomp(self, instruction: Instruction) -> str:
        """Handle the ASSERT_EQ opcode

        Returns:
            String: The formated ASSERT_EQ instruction
        """
        source_code = ""

        # Registers and offsets
        destination_register = instruction.dstRegister.lower()
        destination_offset = int(instruction.offDest) if instruction.offDest else 0
        op0_register = instruction.op0Register.lower()
        offset_1 = int(instruction.off1) if instruction.off1 else 0   
        op1_register = instruction.op1Addr.lower()
        offset_2 = int(instruction.off2) if instruction.off2 else 0   
        
        OPERATORS = {"ADD": "+", "MUL": "*"}

        if "OP1" in instruction.res:
            if "IMM" in instruction.op1Addr:
                value = utils.value_to_string(int(instruction.imm), (instruction.prime))
                if value == "":
                    value = utils.field_element_repr(int(instruction.imm), instruction.prime)
                source_code += self.print_instruction_decomp(
                    f"{self.ssa.get_variable(destination_register, destination_offset)} = {utils.field_element_repr(int(instruction.imm), instruction.prime)}",
                    color=utils.color.GREEN
                )
                # Variable value (hex or string)
                source_code += self.print_instruction_decomp(
                    f" -> {value}",
                    color=utils.color.CYAN,
                )
            elif "OP0" in instruction.op1Addr:
                source_code += self.print_instruction_decomp(
                    f"{self.ssa.get_variable(destination_register, destination_offset)} = [{self.ssa.get_variable(op0_register, offset_1)}{instruction.off2}]",
                    color=utils.color.GREEN
                )
            else:
                source_code += self.print_instruction_decomp(
                    f"{self.ssa.get_variable(destination_register, destination_offset)} = {self.ssa.get_variable(op1_register, offset_2)}",
                    color=utils.color.GREEN
                )
        else:
            op = OPERATORS[instruction.res]
            if "IMM" not in instruction.op1Addr:
                source_code += self.print_instruction_decomp(           
                    f"{self.ssa.get_variable(destination_register, destination_offset)} = {self.ssa.get_variable(op0_register, offset_1)} {op} {self.ssa.get_variable(op1_register, offset_2)}",
                    color=utils.color.GREEN
                )
            else:
                source_code += self.print_instruction_decomp(
                    f"{self.ssa.get_variable(destination_register, destination_offset)} = {self.ssa.get_variable(op0_register, offset_1)} {op} {utils.field_element_repr(int(instruction.imm), instruction.prime)}",
                    color=utils.color.GREEN
                )
                
        return source_code

    def _handle_nop_decomp(self, instruction: Instruction) -> str:
        """Handle the NOP opcode

        Returns:
            String: The formated NOP instruction
        """
        source_code = ""

        destination_offset = int(instruction.offDest) if instruction.offDest else 0

        if "REGULAR" not in instruction.pcUpdate:
            if instruction.pcUpdate == "JNZ":
                source_code += (
                    self.print_instruction_decomp(f"if ", color=utils.color.RED)
                    + f"{self.ssa.get_variable('ap', destination_offset)} == 0:"
                )
                self.tab_count += 1
                self.ifcount += 1
                # Detect if there is an else later
                jump_to = int(
                    utils.field_element_repr(int(instruction.imm), instruction.prime)
                ) + int(instruction.id)
                for inst in self.decompiled_function.instructions:
                    if int(inst.id) == int(jump_to) - 2 or int(inst.id) == int(jump_to) - 1:
                        if inst.pcUpdate != "JUMP_REL":
                            self.end_if = int(jump_to)
                            self.ifcount -= 1
            elif instruction.pcUpdate == "JUMP_REL":
                if self.ifcount != 0:
                    self.tab_count -= 1
                    source_code += self.print_instruction_decomp("else:", color=utils.color.RED)
                    self.tab_count += 1
                    self.end_else.append(
                        int(utils.field_element_repr(int(instruction.imm), instruction.prime))
                        + int(instruction.id)
                    )
                    self.ifcount -= 1
                else:
                    source_code += self.print_instruction_decomp(f"jmp rel {instruction.imm}")
        return source_code

    def _handle_call_decomp(self, instruction: Instruction) -> str:
        """Handle the CALL opcode

        Returns:
            String: The formated CALL instruction
        """
        # Direct CALL or Relative CALL
        source_code = ""

        call_type = "call abs" if instruction.is_call_abs() else "call rel"
        if instruction.is_call_direct():
            offset = int(utils.field_element_repr(int(instruction.imm), instruction.prime))
            # direct CALL to a fonction
            if instruction.call_xref_func_name is not None:
                call_name = instruction.call_xref_func_name.split(".")
                args = 0
                for function in self.functions:
                    # print(function.name, [_.name for _ in self.ssa.memory], self.ssa.ap_position)
                    if function.name == instruction.call_xref_func_name:
                        if function.args != None:
                            args += len(function.args)
                        if function.implicitargs != None:
                            args += len(function.implicitargs)
                args_str = ""
                while args != 0:
                    args_str += f"{self.ssa.get_variable('ap', -1 * int(args))}"
                    if args != 1:
                        args_str += ", "
                    args -= 1
                source_code += (
                    self.print_instruction_decomp(f"{call_name[-1]}", color=utils.color.RED)
                    + f"({args_str})"
                )
            # CALL to a label
            # e.g. call rel (123)
            else:
                source_code += self.print_instruction_decomp(
                    f"{call_type} ({offset})", color=utils.color.RED
                )
                if str(offset) in instruction.labels:
                    source_code += self.print_instruction_decomp(
                        f"# {instruction.labels[str(offset)]}",
                        color=utils.color.CYAN,
                    )
        # CALL
        # e.g. call rel [fp + 4]
        elif instruction.is_call_indirect():
            source_code += self.print_instruction_decomp(
                f"{call_type} [{instruction.op1Addr}{instruction.off2}]"
            )
        else:
            raise NotImplementedError
        return source_code

    def _handle_ret_decomp(self, last: bool = False) -> str:
        """Handle the RET opcode

        Returns:
            String: The formated RET instruction
        """
        source_code = ""

        if self.return_values == None:
            source_code += self.print_instruction_decomp("ret", end="\n", color=utils.color.RED)
            if last:
                self.tab_count -= 1
        else:
            idx = len(self.return_values)
            source_code += self.print_instruction_decomp("return", color=utils.color.RED) + "("
            while idx:
                source_code += f"{self.ssa.get_variable('ap', -1 * int(idx))}"
                if idx != 1:
                    source_code += ", "
                idx -= 1
            source_code += ")\n"
        if last:
            self.tab_count = 0
            source_code += self.print_instruction_decomp("end", color=utils.color.RED)
        return source_code

    def _handle_hint_decomp(self, instruction: Instruction) -> str:
        """Handle the hint

        Returns:
            String: The formated hint
        """
        source_code = ""

        hints = instruction.hint.split("\n")
        source_code += self.print_instruction_decomp("%{ ", end="\n")
        self.tab_count += 1
        for hint in hints:
            source_code += self.print_instruction_decomp(hint, end="\n")
        self.tab_count -= 1
        source_code += self.print_instruction_decomp("%} ", end="\n")
        return source_code

    def print_build_code(self, instruction: Instruction, last: bool = False) -> str:
        """Read the instruction and print each element of it

        Raises:
            AssertionError: Should never happen - Unknown opcode

        Returns:
            String: String containing the instruction line with the offset ...
        """
        source_code = ""

        if instruction.id in instruction.labels:
            source_code += self.print_instruction_decomp(
                f"\nLABEL : {instruction.labels[instruction.id]}",
                color=utils.color.GREEN,
            )
        if instruction.hint:
            source_code += self._handle_hint_decomp(instruction)

        if "ASSERT_EQ" in instruction.opcode:
            source_code += self._handle_assert_eq_decomp(instruction)
            if "REGULAR" not in instruction.apUpdate:
                source_code += ";"
                op = list(filter(None, re.split(r"(\d+)", instruction.apUpdate)))
                APval = (
                    op[1]
                    if (len(op) > 1)
                    else int(utils.field_element_repr(int(instruction.imm), instruction.prime))
                )
        elif "NOP" in instruction.opcode:
            source_code += self._handle_nop_decomp(instruction)
        elif "CALL" in instruction.opcode:
            source_code += self._handle_call_decomp(instruction)
        elif "RET" in instruction.opcode:
            source_code += self._handle_ret_decomp(last=last)
        else:
            raise AssertionError
        return source_code

    def print_instruction_decomp(
        self, data: str, color: str = "", end: str = "", tab_count: int = None
    ) -> str:
        """format the instruction

        Args:
            data (String): Data to print
            color (str, optional): Color to use. Defaults to "".
            end (str, optional): End of the string. Defaults to "".
            tab (int): Number of tabulation
        Returns:
            String: The formated Instruction
        """
        tabulation = "    "

        if tab_count is not None:
            tabulations = tabulation * tab_count
        else:
            tabulations = tabulation * self.tab_count

        decompiled_instruction = color + tabulations + data + utils.color.ENDC + end
        return decompiled_instruction

    def decompile_code(self) -> str:
        source_code = ""

        for function in self.functions:
            self.tab_count = 0
            count = 0

            # Create new variables in memory for function arguments and return values
            if len(function.arguments_list()) != 0:
                for argument in function.arguments_list():
                    self.ssa.new_variable(variable_name=argument)
            self.ssa.new_variable()
            self.ssa.new_function_init()
            
            if function.is_import is False:

                source_code += "\n"
                self.decompiled_function = function
                self.return_values = function.ret

                function.generate_cfg()

                source_code += self.print_instruction_decomp(
                    function.get_prototype(), end="\n", color=utils.color.BLUE
                )
                self.tab_count += 1

                if function.cfg.basicblocks != []:
                    for block in function.cfg.basicblocks:
                        for instruction in block.instructions:
                            if int(instruction.id) == self.end_if:
                                self.end_if = None
                                self.tab_count -= 1
                                source_code += self.print_instruction_decomp(
                                    "end", end="\n", color=utils.color.RED
                                )
                            if self.end_else != []:
                                for idx in range(len(self.end_else)):
                                    if self.end_else[idx] == int(instruction.id):
                                        self.tab_count -= 1
                                        source_code += self.print_instruction_decomp(
                                            "end",
                                            end="\n",
                                            color=utils.color.RED,
                                        )
                                        # del self.end_else[idx]

                            count += 1
                            instruction = self.print_build_code(
                                instruction,
                                last=(count == len(function.instructions)),
                            )
                            source_code += instruction + "\n"
        return source_code
