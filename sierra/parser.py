import config
from lark import Lark
from lark.reconstruct import Reconstructor
from lark.tree import Tree
from typing import List

from objects import SierraFunction, SierraLibFunc, SierraStatement, SierraType


class SierraParser:
    """
    Sierra Parser class
    """

    def __init__(self, lark_parser_path: str) -> None:
        """
        Sierra Parser initialization
        """
        # Lark parser
        self.parser = Lark.open(lark_parser_path, ambiguity="explicit", maybe_placeholders=False)
        # Lark reconstructor
        self.reconstructor = Reconstructor(self.parser)

        # Sierra objects
        self.types: List[SierraType] = []
        self.statements: List[SierraStatement] = []
        self.libfuncs: List[SierraLibFunc] = []
        self.functions: List[SierraFunction] = []

    def _handle_type_definition(self, type_definition: Tree) -> None:
        """
        Handle sierra type definition
        """
        concrete_type_id = list(type_definition.find_data("concrete_type_id"))
        type_name = self.reconstructor.reconstruct(concrete_type_id[-1])
        self.types.append(SierraType(name=type_name))

    def _handle_libfunc_definition(self, libfunc_definition: Tree) -> None:
        """
        Handle sierra libfunc definition
        """
        concrete_libfunc_id = list(libfunc_definition.find_data("concrete_libfunc_id"))
        libfunc_name = self.reconstructor.reconstruct(concrete_libfunc_id[-1])
        self.libfuncs.append(SierraLibFunc(name=libfunc_name))

    def _handle_statement(self, statement: Tree) -> None:
        """
        Handle sierra statement definition
        """
        return

    def _handle_function_declaration(self, function_declaration: Tree) -> None:
        """
        Handle sierra function definition
        """
        return

    def parse(self, sierra_file_path: str) -> None:
        """
        Parse a sierra file
        """
        # Load source code from file
        with open(sierra_file_path, "r") as f:
            sierra_code = f.read()

        # Generate a tree from the Sierra source code using the LARK Parser
        try:
            tree = self.parser.parse(sierra_code)
        except:
            return

        # Parse type definitions
        type_definitions = list(tree.find_data("type_declaration"))
        for type_definition in type_definitions:
            self._handle_type_definition(type_definition)

        # Parse libfunc declarations
        libfunc_declarations = list(tree.find_data("libfunc_declaration"))
        for libfunc_declaration in libfunc_declarations:
            self._handle_libfunc_definition(libfunc_declaration)

        statements = list(tree.find_data("statement"))
        function = list(tree.find_data("function"))
