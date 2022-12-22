from graphviz import Digraph
from lark import Lark
from lark.reconstruct import Reconstructor
from typing import List, Optional
from sierra.config import CFG_EDGE_ATTR, CFG_GRAPH_ATTR, CFG_NODE_ATTR

from sierra.objects.objects import (
    SierraFunction,
    SierraLibFunc,
    SierraStatement,
    SierraType,
    SierraVariable,
)


class SierraParser:
    """
    Sierra Parser class
    """

    # Handlers
    from ._handlers import (
        _handle_function_declaration,
        _handle_libfunc_definition,
        _handle_statement,
        _handle_type_definition,
        _handle_variable_assignation,
        _handle_fallthrough,
        _handle_control_flow_command,
        _handle_return,
    )

    def __init__(self, lark_parser_path: str) -> None:
        """
        Sierra Parser initialization
        """
        # Lark parser
        self.parser = Lark.open(lark_parser_path, ambiguity="explicit", maybe_placeholders=False)
        # Lark reconstructor
        self.reconstructor = Reconstructor(self.parser)

        # Parsed statements
        self.types: List[SierraType] = []
        self.libfuncs: List[SierraLibFunc] = []
        self.statements: List[SierraStatement] = []
        self.functions: List[SierraFunction] = []

        # Defined variables
        self.variables: List[SierraVariable] = []

    def _get_type_by_id(self, type_id: str) -> Optional[SierraType]:
        """
        Find a type by id among the declared types
        """
        type_match = [t for t in self.types if t.id == type_id]
        return type_match

    def _get_variable_by_name(self, name: str, type: SierraType = None) -> None:
        """
        Find a variable using the name among the declared variables
        Create the variable if it does not exist
        """
        variable_by_name = [v for v in self.variables if v.name == name]
        # If the variable already exists
        if variable_by_name:
            variable = variable_by_name[0]
        # Create a new variable if the variable does not exist
        else:
            variable = SierraVariable(name=name, type=type)
            # Append the variable to the global defined variables list
            self.variables.append(variable)

        return variable

    def _get_libfunc_by_id(self, id: str) -> SierraLibFunc:
        """
        Find a libfunc by id among the declared libfuncs
        """
        libfunc_match = [l for l in self.libfuncs if l.id == id][0]
        return libfunc_match

    def _load_functions_statements(self) -> None:
        """
        Load statements into functions objects
        """
        # Set the end offset for every function
        for i in range(1, len(self.functions)):
            self.functions[i - 1].end_offset = self.functions[i].start_offset
        self.functions[-1].end_offset = len(self.statements)

        # Find the corresponding statements for each function
        for function in self.functions:
            function_statements = [
                s
                for s in self.statements
                if function.start_offset <= s.offset < function.end_offset
            ]
            function.statements = function_statements

    def parse(self, sierra_file_path: str) -> None:
        """
        Parse a sierra file
        """
        # Load source code from file
        with open(sierra_file_path, "r") as f:
            sierra_code = f.read()

        # Generate a tree from the Sierra source code using the LARK Parser
        tree = self.parser.parse(sierra_code)

        # Parse type definitions
        type_definitions = list(tree.find_data("type_declaration"))
        for type_definition in type_definitions:
            self._handle_type_definition(type_definition)

        # Parse libfunc declarations
        libfunc_declarations = list(tree.find_data("libfunc_declaration"))
        for libfunc_declaration in libfunc_declarations:
            self._handle_libfunc_definition(libfunc_declaration)

        # Parse functions
        functions = list(tree.find_data("function"))
        for function in functions:
            self._handle_function_declaration(function)

        # Parse statements
        statements = list(tree.find_data("statement"))
        for statement in statements:
            self._handle_statement(statement)

        # Load statements into functions objects
        self._load_functions_statements()

        # Create basic blocks
        for function in self.functions:
            function.cfg._generate_basic_blocks()

    def print_cfg(self, folder: str, file_format: str) -> None:
        """
        Print the CFG dot graph
        """
        graph = Digraph(
            name="cfg",
            node_attr=CFG_NODE_ATTR,
            graph_attr=CFG_GRAPH_ATTR,
            edge_attr=CFG_EDGE_ATTR,
        )
        for function in self.functions:
            function.cfg._generate_cfg()
            graph.subgraph(function.cfg.dot)

        print(file_format)
        graph.format = file_format
        graph.render(directory=folder, view=True)
