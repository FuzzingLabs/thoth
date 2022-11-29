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

    from thoth.app.decompiler._instruction_handlers import (
        _handle_assert_eq_decomp,
        _handle_call_decomp,
        _handle_hint_decomp,
        _handle_nop_decomp,
        _handle_ret_decomp,
    )

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
        Variable.counter = 0
        BasicBlock.counter = 0
        self.ssa = SSA()
        self.defined_variables: List[Variable] = []
        self.assertion = False
        self.current_basic_block: Optional[BasicBlock] = None
        self.first_pass = True
        self.block_new_variables = 0
        # Function calls
        self.function_calls = 0

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

    def decompile_code(self, first_pass_only: bool = False) -> str:
        """
        Decompile the contract code
        Return the decompiled code
        """
        source_code = ""

        for function in self.functions:
            # self.first_pass = True
            self.current_function = function
            self.tab_count = 0
            count = 0

            # Initialize AP and FP registers values at the  beginning of the function
            self.ssa.new_function_init(function)

            # Imported function
            if function.is_import:
                continue

            # Create a backup value of AP and FP registers
            ap_backup_value = self.ssa.ap_position
            fp_backup_value = self.ssa.fp_position

            self.decompiled_function = function
            self.return_values = function.ret

            function.generate_cfg()

            # Print the function ID as a comment before the prototype
            source_code += self.print_instruction_decomp(
                f"// Function {function.id}", end="\n", color=utils.color.CYAN
            )
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

            # Speed the decompilation process for the analyzers by
            # doing only one pass
            if first_pass_only:
                continue

            # Initialize the SSA for the second pass
            self.ssa.ap_position = ap_backup_value
            self.ssa.fp_position = fp_backup_value
            self.tab_count = 1
            self.end_else = []
            self.ifcount = 0
            self.end_if = None
            for v in self.ssa.memory:
                v.value = None

            self.first_pass = False
            for block in function.cfg.basicblocks:

                self.current_basic_block = block
                self.block_new_variables = 0
                instructions = block.instructions
                for i in range(len(instructions)):
                    self.assertion = False
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
                        instructions[i], last=(count == len(function.instructions))
                    )
                    source_code += instructions[i]
                    source_code += "\n"
            source_code += "\n"

        # Remove useless spaces
        source_code = source_code.strip()
        return source_code
