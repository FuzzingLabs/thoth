import re
from typing import List, Tuple
from thoth.app import utils
from thoth.app.cfg.cfg import BasicBlock
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
        self.max_new_variables: List[int] = []
        self.current_basic_block = BasicBlock

    def get_max_new_variables(
        self, instructions: List[Instruction], instruction_offset: int
    ) -> Tuple[int]:
        """ """
        if_count = 0
        max_new_variables = [0, 0]
        branch = 0

        end_if = []
        end_else = []
        # Is there an else
        for i in range(instruction_offset, len(instructions)):
            # If instructions
            if instructions[i].pcUpdate == "JNZ":
                jump_to = int(
                    utils.field_element_repr(int(instructions[i].imm), instructions[i].prime)
                ) + int(instructions[i].id)
                for j in range(i, len(instructions)):
                    if (
                        int(instructions[j].id) == int(jump_to) - 2
                        or int(instructions[j].id) == int(jump_to) - 1
                    ):
                        if instructions[j].pcUpdate != "JUMP_REL":
                            end_if.append(int(jump_to))
                if_count += 1
            elif instructions[i].pcUpdate == "JUMP_REL":
                if if_count != 0:
                    branch = 1
                    jump_to = int(
                        utils.field_element_repr(int(instructions[i].imm), instructions[i].prime)
                    ) + int(instructions[i].id)
                    for j in range(i, len(instructions)):
                        if (
                            int(instructions[j].id) == int(jump_to) - 2
                            or int(instructions[j].id) == int(jump_to) - 1
                        ):
                            end_else.append(int(jump_to))
            # Ap incrementations
            elif "REGULAR" not in instructions[i].apUpdate:
                op = list(filter(None, re.split(r"(\d+)", instructions[i].apUpdate)))
                APval = (
                    op[1]
                    if (len(op) > 1)
                    else int(
                        utils.field_element_repr(int(instructions[i].imm), instructions[i].prime)
                    )
                )
                # Update AP register value
                max_new_variables[branch] += int(APval)
            if len(end_else) != 0:
                if int(instructions[i].id) == int(end_else[-1]):
                    if_count -= 1
            if len(end_if) != 0:
                if int(instructions[i].id) == int(end_if[-1]):
                    if_count -= 1
                    end_if.pop()
            if if_count == 0:
                break
        return max_new_variables

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

        destination_offset = int(instruction.offDest) if instruction.offDest else 0
        if "OP1" in instruction.res:
            if "IMM" in instruction.op1Addr:
                value = utils.value_to_string(int(instruction.imm), (instruction.prime))
                if value == "":
                    value = utils.field_element_repr(int(instruction.imm), instruction.prime)

                variable = self.ssa.get_variable(destination_register, destination_offset)
                source_code += self.print_instruction_decomp(
                    f"{variable[1]} = {utils.field_element_repr(int(instruction.imm), instruction.prime)}",
                    color=utils.color.GREEN,
                )
                # Variable value (hex or string)
                source_code += self.print_instruction_decomp(
                    f" # {value}",
                    color=utils.color.CYAN,
                )
            elif "OP0" in instruction.op1Addr:
                variable = self.ssa.get_variable(destination_register, destination_offset)
                value_off2 = instruction.off2
                sign = ""
                try:
                    value_off2 = int(value_off2)
                    sign = " + " if value_off2 >= 0 else " - "
                except Exception:
                    pass
                source_code += self.print_instruction_decomp(
                    f"{variable[1]} = [{self.ssa.get_variable(op0_register, offset_1, True)[1]}{sign}{value_off2}]",
                    color=utils.color.GREEN,
                )
            else:
                variable = self.ssa.get_variable(destination_register, destination_offset)
                source_code += self.print_instruction_decomp(
                    f"{variable[1]} = {self.ssa.get_variable(op1_register, offset_2, True)[1]}",
                    color=utils.color.GREEN,
                )
        else:
            op = OPERATORS[instruction.res]
            if "IMM" not in instruction.op1Addr:
                variable = self.ssa.get_variable(destination_register, destination_offset)
                source_code += self.print_instruction_decomp(
                    f"{variable[1]} = {self.ssa.get_variable(op0_register, offset_1, True)[1]} {op} {self.ssa.get_variable(op1_register, offset_2, True)[1]}",
                    color=utils.color.GREEN,
                )
            else:
                variable = self.ssa.get_variable(destination_register, destination_offset)
                value = int(utils.field_element_repr(int(instruction.imm), instruction.prime))
                if value < 0 and op == "+":
                    op = "-"
                    value = -value
                source_code += self.print_instruction_decomp(
                    f"{variable[1]} = {self.ssa.get_variable(op0_register, offset_1, True)[1]} {op} {value}",
                    color=utils.color.GREEN,
                )
        return source_code

    def _handle_nop_decomp(self, instruction: Instruction, offset: int) -> str:
        """Handle the NOP opcode

        Returns:
            String: The formated NOP instruction
        """
        source_code = ""

        destination_offset = int(instruction.offDest) if instruction.offDest else 0

        if "REGULAR" not in instruction.pcUpdate:
            if instruction.pcUpdate == "JNZ":
                self.max_new_variables.append(self.get_max_new_variables(self.instructions, offset))
                ap_offset = max(self.max_new_variables[-1]) - self.max_new_variables[-1][0]
                self.ssa.new_if_branch(ap_offset)
                source_code += (
                    self.print_instruction_decomp(f"if ", color=utils.color.RED)
                    + f"{self.ssa.get_variable('ap', destination_offset)[1]} == 0:"
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
                    ap_offset = max(self.max_new_variables[-1]) - self.max_new_variables[-1][1]
                    self.ssa.new_else_branch(ap_offset)
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
                    if function.name == instruction.call_xref_func_name:
                        if function.args != None:
                            args += len(function.args)
                        if function.implicitargs != None:
                            args += len(function.implicitargs)
                args_str = ""
                while args != 0:
                    args_str += f"{self.ssa.get_variable('ap', -1 * int(args))[1]}"
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
                source_code += f"{self.ssa.get_variable('ap', -1 * int(idx))[1]}"
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

    def print_build_code(self, instruction: Instruction, offset: int, last: bool = False) -> str:
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
                # Update AP register value
                for i in range(int(APval)):
                    self.ssa.ap_position += 1
                    pass
        elif "NOP" in instruction.opcode:
            source_code += self._handle_nop_decomp(instruction, offset)
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
        """
        Decompile the contract code
        Return the decompiled code
        """
        source_code = ""

        for function in self.functions:
            self.tab_count = 0
            count = 0

            # Create new variables in memory for function arguments and return values
            if len(function.arguments_list()) != 0:
                for argument in function.arguments_list():
                    self.ssa.new_variable(variable_name=argument)
                    self.ssa.ap_position += 1

            # Imported function
            if function.is_import:
                continue

            # Initialize AP and FP registers values at the  beginning of the function
            self.ssa.new_function_init()

            self.decompiled_function = function
            self.return_values = function.ret

            function.generate_cfg()

            source_code += self.print_instruction_decomp(
                function.get_prototype(), end="\n", color=utils.color.BLUE
            )
            self.tab_count += 1

            # If there are no basic blocks
            if function.cfg.basicblocks == []:
                return source_code

            # Create a list with all instructions
            instructions = []
            for i in range(len(function.cfg.basicblocks)):
                block = function.cfg.basicblocks[i]
                instructions.append(block.instructions)
            instructions = sum(instructions, [])
            self.instructions = instructions

            # Iterate through basic blocks
            for block in function.cfg.basicblocks:
                instructions = block.instructions
                is_phi_node = block.is_phi_node
                for i in range(len(instructions)):
                    if int(instructions[i].id) == self.end_if:
                        self.max_new_variables.pop()
                        self.end_if = None
                        self.tab_count -= 1
                        source_code += self.print_instruction_decomp(
                            "end", end="\n", color=utils.color.RED
                        )
                    if self.end_else != []:
                        for idx in range(len(self.end_else)):
                            if self.end_else[idx] == int(instructions[i].id):
                                self.tab_count -= 1
                                self.ssa.end_if_branch()
                                source_code += self.print_instruction_decomp(
                                    "end",
                                    end="\n",
                                    color=utils.color.RED,
                                )

                    count += 1
                    instructions[i] = self.print_build_code(
                        instructions[i],
                        i,
                        last=(count == len(function.instructions)),
                    )
                    source_code += instructions[i]
                    source_code += "\n"
                source_code += "\n"
        return source_code
