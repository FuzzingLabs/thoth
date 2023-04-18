import re
from graphviz import Digraph
from sierra.config import (
    CALLGRAPH_EDGE_ATTR,
    CALLGRAPH_GRAPH_ATTR,
    CALLGRAPH_LIBFUNCS_COLOR,
    CALLGRAPH_NODE_ATTR,
    CALLGRAPH_USER_DEFINED_FUNCTIONS_COLOR,
)
from sierra.objects.objects import SierraVariableAssignation
from sierra.parser.parser import SierraParser

# User defined function are called using a libfunc named
# function_call<user@function_id>
USER_DEFINED_FUNCTION_REGEXP = re.compile(
    r"(function_call|(\[[0-9]+\]))(::)?<user@(?P<function_id>.+)>"
)


class SierraCallGraph:
    """
    Sierra Call-Graph class
    """

    def __init__(self, program: SierraParser) -> None:
        # Parsed sierra program
        self.program = program
        # Dot graph
        self.dot = None

    def generate_callgraph(self) -> None:
        """
        Generate a call-graph dot graph
        """
        self.dot = Digraph(
            name="Call-Flow Graph",
            strict=True,
            node_attr=CALLGRAPH_NODE_ATTR,
            graph_attr=CALLGRAPH_GRAPH_ATTR,
            edge_attr=CALLGRAPH_EDGE_ATTR,
        )

        functions = self.program.functions
        for function in functions:
            # Create a node for the source function
            source_function_name = self.sanitize_name(function.id)
            self.dot.node(
                name=source_function_name,
                shape="rectangle",
                fillcolor=CALLGRAPH_USER_DEFINED_FUNCTIONS_COLOR,
            )

            # Find all functions called inside source function
            for statement in function.statements:
                if isinstance(statement, SierraVariableAssignation):
                    called_function = statement.function

                # Call to an user defined function
                if self._is_user_defined_function(called_function.id):
                    # Create a node for an user defined function
                    called_function_name = USER_DEFINED_FUNCTION_REGEXP.match(
                        called_function.name
                    ).group(4)

                    called_function_name = self.sanitize_name(called_function_name)
                    self.dot.node(
                        name=called_function_name,
                        shape="rectangle",
                        fillcolor=CALLGRAPH_USER_DEFINED_FUNCTIONS_COLOR,
                    )

                # Call to a libfunc function
                else:
                    # Create a node for a libfunc
                    if called_function.name != called_function.id:
                        called_function_name = self.sanitize_name(called_function.name)
                    else:
                        called_function_name = self.sanitize_name(called_function.id)
                    self.dot.node(
                        name=called_function_name,
                        shape="ellipse",
                        fillcolor=CALLGRAPH_LIBFUNCS_COLOR,
                    )

                # Create an edge between the source function and the called function
                self.dot.edge(source_function_name, called_function_name)

    def _is_user_defined_function(self, function_name: str) -> bool:
        """
        Returns True if function_name matches the regex for user-defined functions,
        False otherwise.
        """
        return bool(USER_DEFINED_FUNCTION_REGEXP.match(function_name))

    def sanitize_name(self, name: str) -> str:
        """
        Replace ":" with "𐫵" and return the resulting string.
        """
        return name.replace(":", "𐫵")

    def print_callgraph(self, folder: str, file_format: str, view: bool = True) -> None:
        """
        Render the dot call-graph
        """
        self.dot.format = file_format
        self.dot.render(directory=folder, view=view)
