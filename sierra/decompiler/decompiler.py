from typing import Optional

from sierra.objects.objects import (
    EDGE_CONDITIONAL_FALSE,
    EDGE_CONDITIONAL_TRUE,
    SierraBasicBlock,
    SierraConditionalBranch,
    SierraFunction,
)
from sierra.parser.parser import SierraParser
from sierra.utils import colors


class SierraDecompiler:
    """
    Sierra Decompiler class
    """

    def __init__(self, program: SierraParser) -> None:
        """
        Initialize the decompiler
        """
        self.program = program
        self.indentation = 1
        self.printed_blocks = []
        self.current_function: Optional[SierraFunction] = None

    def _basic_block_to_str(self, basic_block: SierraBasicBlock) -> str:
        """
        Convert a Sierra BasicBlock object to a string
        """
        # Don't print 2 times the same block
        if basic_block in self.printed_blocks:
            return ""
        self.printed_blocks.append(basic_block)

        # Initialize the basic block string
        decompiled_basic_block = ""
        indentation = self.indentation * "\t"

        # Append each statement to the string block
        for statement in basic_block.statements:
            # If condition
            if isinstance(statement, SierraConditionalBranch) and len(basic_block.edges) == 2:
                function_name = statement.function
                function_arguments = ", ".join([v.name for v in statement.parameters])
                decompiled_basic_block += "%sif (%s(%s) == 0) %s{%s\n" % (
                    indentation,
                    function_name,
                    function_arguments,
                    colors.GREEN,
                    colors.ENDC,
                )
            # Unconditional jump
            elif isinstance(statement, SierraConditionalBranch):
                pass
            # Default case
            else:
                decompiled_basic_block += "%s%s\n" % (indentation, statement.formatted_statement)

        return decompiled_basic_block

    def _basic_block_recursive(self, basic_block: SierraBasicBlock) -> str:
        """
        Recursively (nested conditions) convert basic blocks to string
        """

        # Initialize the basic blocks string
        basic_blocks_str = ""

        # Add the root basic block
        basic_blocks_str += self._basic_block_to_str(basic_block)

        # Add the edges
        for edge in basic_block.edges:
            # If branch
            if edge.type == EDGE_CONDITIONAL_TRUE:
                self.indentation += 1
                edge_basic_block = [
                    b
                    for b in self.current_function.cfg.basic_blocks
                    if edge.destination == b.start_offset
                ][0]
                basic_blocks_str += self._basic_block_recursive(edge_basic_block)
                self.indentation -= 1
            # Else branch
            elif edge.type == EDGE_CONDITIONAL_FALSE:
                edge_basic_block = [
                    b
                    for b in self.current_function.cfg.basic_blocks
                    if edge.destination == b.start_offset
                ][0]
                if edge_basic_block not in self.printed_blocks:
                    basic_blocks_str += (
                        "\t" * self.indentation
                        + colors.GREEN
                        + "}"
                        + colors.ENDC
                        + " else "
                        + colors.GREEN
                        + "{\n"
                        + colors.ENDC
                    )
                    self.indentation += 1
                    basic_blocks_str += self._basic_block_recursive(edge_basic_block)
                    self.indentation -= 1
                    basic_blocks_str += colors.GREEN + "\t" * self.indentation + "}\n" + colors.ENDC

        return basic_blocks_str

    def _get_function_prototype(self, function: SierraFunction) -> str:
        """
        Return the formatted function prototype
        func <name> (<arguments, ...>) -> (<return values, ...>)
        """

        # Prototype elements
        function_name = function.id
        function_arguments = ", ".join(
            ["%s: %s" % (a.representation_name, a.type[0].id) for a in function.parameters]
        )
        function_return_values = (
            "(" + ", ".join([t[0].id for t in function.return_values_types]) + ")"
        )

        # Format the prototype
        prototype = "func %s (%s) -> %s" % (
            function_name,
            function_arguments,
            function_return_values,
        )
        return prototype

    def decompile_code(self) -> str:
        """
        Decompile the sierra program
        """

        # Initialize the decompiled code
        decompiled_code = ""

        # Decompile the functions
        functions = self.program.functions
        for i in range(len(functions)):
            self.current_function = functions[i]

            # Iniialize indentation
            self.indentation = 1

            # Prototype
            function_prototype = self._get_function_prototype(self.current_function)
            # Function body
            decompiled_code += colors.HEADER + function_prototype + colors.ENDC + "\n"
            decompiled_code += colors.GREEN + "{" + colors.ENDC
            decompiled_code += "\n"
            basic_blocks = self.current_function.cfg.basic_blocks
            for basic_block in basic_blocks:
                decompiled_code += self._basic_block_recursive(basic_block=basic_block)
            decompiled_code += colors.GREEN + "}" + colors.ENDC

            # Space between functions
            if i != len(functions) - 1:
                decompiled_code += "\n\n"

        return decompiled_code
