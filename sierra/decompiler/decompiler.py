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
                try:
                    self.indentation += 1
                    edge_basic_block = [
                        b
                        for b in self.current_function.cfg.basic_blocks
                        if edge.destination == b.start_offset
                    ][0]
                    basic_blocks_str += self._basic_block_recursive(edge_basic_block)
                # Handle empty if condition block
                except Exception:
                    pass
                self.indentation -= 1
            # Else branch
            elif edge.type == EDGE_CONDITIONAL_FALSE:
                try:
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
                # Handle empty else condition block
                except Exception:
                    pass
                self.indentation -= 1
                basic_blocks_str += colors.GREEN + "\t" * self.indentation + "}\n" + colors.ENDC

        return basic_blocks_str

    def _types(self) -> str:
        """
        Return a string containing all the types definitions
        """
        types = ""
        for type in self.program.types:
            types += type.formatted_type
            types += "\n"

        return types

    def _libfuncs(self) -> str:
        """
        Return a libfunc containing all the types definitions
        """
        libfuncs = ""
        for libfunc in self.program.libfuncs:
            libfuncs += libfunc.formatted_libfunc
            libfuncs += "\n"

        return libfuncs

    def decompile_code(self) -> str:
        """
        Decompile the sierra program
        """

        # Initialize the decompiled code
        decompiled_code = ""

        # Add types definitions
        decompiled_code += self._types()
        decompiled_code += "\n"

        # Add libfuncs
        decompiled_code += self._libfuncs()
        decompiled_code += "\n"

        # Decompile the functions
        functions = self.program.functions
        for i in range(len(functions)):
            self.current_function = functions[i]

            # Iniialize indentation
            self.indentation = 1

            # Prototype
            function_prototype = self.current_function.prototype
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
