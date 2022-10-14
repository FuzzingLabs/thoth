import copy
import re
from typing import List, Optional
from thoth.app import utils
from thoth.app.cfg.cfg import BasicBlock
from thoth.app.disassembler.function import Function
from thoth.app.disassembler.instruction import Instruction
from thoth.app.decompiler.ssa import SSA
from thoth.app.decompiler.variable import Variable


class Decompiler:
    """
    Decompiler class

    decompile bytecodes
    """

    def __init__(self, functions: List[Function]) -> None:
        """
        Args:
            functions (List Function): list of the functions to decompile
        """
        self.tab_count = 1
        self.end_else = []
        self.ifcount = 0
        self.end_if = None
        self.functions = functions
        self.decompiled_function = None
        self.return_values = None
        # Static single assignment
        self.ssa = SSA()
        self.current_basic_block: Optional[BasicBlock] = None
        self.first_pass = True
        self.block_new_variables = 0

    def get_phi_node_variables(self) -> List[Variable]:
        """
        Returns:
            phi_node_variables (List Variable): A list of the variables used in the phi node
        """
        phi_node_variables = []

        parents_list = self.current_function.cfg.parents(self.current_basic_block)
        # Recursively get parents blocks last defined variables
        # Phi function always use variables stored in [AP - 1]
        while parents_list != []:
            if len(parents_list[0].variables) != 0:
                phi_node_variables.append(parents_list[0].variables[-1])
            else:
                parents_list += self.current_function.cfg.parents(parents_list[0])
            parents_list.remove(parents_list[0])
        return phi_node_variables

    def _handle_assert_eq_decomp(self, instruction: Instruction) -> str:
        """Handle the ASSERT_EQ opcode
        Args:
            instruction (Instruction): intruction to decompile
        Returns:
            String: The formated ASSERT_EQ instruction
        """
        source_code = ""

        # Generate the phi function representation
        phi_node_variables = []

        # Generate the phi function representation
        if self.current_basic_block.is_phi_node and not self.first_pass:
            phi_node_variables = self.get_phi_node_variables()
            variables_names = [variable.name for variable in self.get_phi_node_variables()]
            # Phi function is represented in the form Φ(var1, var2, ..., var<n>)
            phi_node_representation = "Φ(%s)" % ", ".join(variables_names)
        elif (
            self.block_new_variables == 0
            and len(self.current_function.cfg.parents(self.current_basic_block)) != 0
        ):
            phi_node_variables = self.get_phi_node_variables()
            if len(phi_node_variables) != 0:
                phi_node_representation = phi_node_variables[-1].name

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
                    f"// {value}",
                    color=utils.color.CYAN,
                    tab_count=1,
                )
            elif "OP0" in instruction.op1Addr:
                variable = self.ssa.get_variable(destination_register, destination_offset)

                if self.ssa.get_variable(op0_register, offset_1)[2] in phi_node_variables:
                    operand = phi_node_representation
                else:
                    operand = self.ssa.get_variable(op0_register, offset_1)[1]

                value_off2 = instruction.off2
                sign = ""
                try:
                    value_off2 = int(value_off2)
                    sign = " + " if value_off2 >= 0 else " - "
                except Exception:
                    pass
                source_code += self.print_instruction_decomp(
                    f"{variable[1]} = [{operand}{sign}{value_off2}]",
                    color=utils.color.GREEN,
                )
            else:
                variable = self.ssa.get_variable(destination_register, destination_offset)
                if self.ssa.get_variable(op1_register, offset_2)[2] in phi_node_variables:
                    variable_value = phi_node_representation
                else:
                    variable_value = self.ssa.get_variable(op1_register, offset_2)[1]

                source_code += self.print_instruction_decomp(
                    f"{variable[1]} = {variable_value}",
                    color=utils.color.GREEN,
                )
        else:
            op = OPERATORS[instruction.res]
            if "IMM" not in instruction.op1Addr:
                variable = self.ssa.get_variable(destination_register, destination_offset)

                if self.ssa.get_variable(op0_register, offset_1)[2] in phi_node_variables:
                    operand_1 = phi_node_representation
                else:
                    operand_1 = self.ssa.get_variable(op0_register, offset_1)[1]
                if self.ssa.get_variable(op1_register, offset_2)[2] in phi_node_variables:
                    operand_2 = phi_node_representation
                else:
                    operand_2 = self.ssa.get_variable(op1_register, offset_2)[1]

                source_code += self.print_instruction_decomp(
                    f"{variable[1]} = {operand_1} {op} {operand_2}",
                    color=utils.color.GREEN,
                )
            else:
                variable = self.ssa.get_variable(destination_register, destination_offset)
                try:
                    value = int(utils.field_element_repr(int(instruction.imm), instruction.prime))
                    if value < 0 and op == "+":
                        op = "-"
                        value = -value
                except Exception:
                    value = instruction.imm

                if self.ssa.get_variable(op0_register, offset_1)[2] in phi_node_variables:
                    operand = phi_node_representation
                elif (
                    self.block_new_variables == 0
                    and len(self.current_function.cfg.parents(self.current_basic_block)) != 0
                ):
                    if len(phi_node_variables) != 0:
                        operand = phi_node_representation
                    else:
                        operand = self.ssa.get_variable(op0_register, offset_1)[1]
                else:
                    operand = self.ssa.get_variable(op0_register, offset_1)[1]

                source_code += self.print_instruction_decomp(
                    f"{variable[1]} = {operand} {op} {value}",
                    color=utils.color.GREEN,
                )
                self.block_new_variables += 1
        return source_code

    def _handle_nop_decomp(self, instruction: Instruction) -> str:
        """Handle the NOP opcode
        Args:
                instruction (Instruction): intruction to decompile
        Returns:
            String: The formated NOP instruction
        """
        source_code = ""

        destination_offset = int(instruction.offDest) if instruction.offDest else 0

        if "REGULAR" not in instruction.pcUpdate:
            if instruction.pcUpdate == "JNZ":
                source_code += (
                    self.print_instruction_decomp(f"if ", color=utils.color.RED)
                    + f"({self.ssa.get_variable('ap', destination_offset)[1]} == 0) {{"
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
        Args:
                instruction (Instruction): intruction to decompile
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
                    phi_node_variables = []
                    # Generate the phi function representation
                    if self.current_basic_block.is_phi_node and not self.first_pass:
                        phi_node_variables = self.get_phi_node_variables()
                        variables_names = [
                            variable.name for variable in self.get_phi_node_variables()
                        ]
                        # Phi function is represented in the form Φ(var1, var2, ..., var<n>)
                        phi_node_representation = "Φ(%s)" % ", ".join(variables_names)
                    if self.ssa.get_variable("ap", -1 * int(args))[2] in phi_node_variables:
                        args_str += f"{phi_node_representation}"
                    else:
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
                        f"// {instruction.labels[str(offset)]}",
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
        Args:
            last (Instruction): intruction to decompile
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
            source_code += self.print_instruction_decomp("}", color=utils.color.ENDC)
        return source_code

    def _handle_hint_decomp(self, instruction: Instruction) -> str:
        """Handle the hint
        Args:
            instruction (Instruction): intruction to decompile
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
        Args:
            instruction (Instruction): intruction to decompile
            offset (int):
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
        """
        Decompile the contract code
        Return the decompiled code
        """
        source_code = ""

        for function in self.functions:
            self.current_function = function
            self.tab_count = 0
            count = 0

            # Imported function
            if function.is_import:
                continue

            # Initialize AP and FP registers values at the  beginning of the function
            self.ssa.new_function_init(function)

            # Create a backup value of AP and FP registers
            ap_backup_value = self.ssa.ap_position
            fp_backup_value = self.ssa.fp_position

            self.decompiled_function = function
            self.return_values = function.ret

            function.generate_cfg()

            source_code += self.print_instruction_decomp(
                function.get_prototype(), color=utils.color.BLUE
            )
            source_code += self.print_instruction_decomp("{", end="\n", color=utils.color.ENDC)
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

            # First pass
            for block in function.cfg.basicblocks:
                self.current_basic_block = block
                self.block_new_variables = 0
                memory_backup = copy.deepcopy(self.ssa.memory)
                instructions = block.instructions
                for i in range(len(instructions)):
                    self.print_build_code(
                        instructions[i],
                        last=(count == len(function.instructions)),
                    )
                block.variables = self.ssa.memory[len(memory_backup) :]

            # Initialize the SSA for the second pass
            self.ssa.ap_position = ap_backup_value
            self.ssa.fp_position = fp_backup_value
            self.tab_count = 1
            self.end_else = []
            self.ifcount = 0
            self.end_if = None

            self.first_pass = False
            for block in function.cfg.basicblocks:

                self.current_basic_block = block
                self.block_new_variables = 0
                instructions = block.instructions
                for i in range(len(instructions)):
                    if int(instructions[i].id) == self.end_if:
                        self.end_if = None
                        self.tab_count -= 1
                        source_code += self.print_instruction_decomp(
                            "}", end="\n", color=utils.color.ENDC
                        )
                    if self.end_else != []:
                        for idx in range(len(self.end_else)):
                            if self.end_else[idx] == int(instructions[i].id):
                                self.tab_count -= 1
                                source_code += self.print_instruction_decomp(
                                    "}",
                                    end="\n",
                                    color=utils.color.ENDC,
                                )
                    count += 1
                    instructions[i] = self.print_build_code(
                        instructions[i],
                        last=(count == len(function.instructions)),
                    )
                    source_code += instructions[i]
                    source_code += "\n"
            source_code += "\n"

        # Remove useless spaces
        source_code = source_code.strip()
        return source_code
