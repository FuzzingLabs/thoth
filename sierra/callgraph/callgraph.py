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
USER_DEFINED_FUNCTION_REGEXP = re.compile(r"function_call(::)?<user@(?P<function_id>.+)>")


class SierraCallGraph:
    """
    Sierra Call-Graph class
    """

    def __init__(self, program: SierraParser) -> None:
        # Parsed sierra program
        self.program = program
        # Dot graph
        self.dot = None

    def _generate_callgraph(self) -> None:
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

            # Bug in Graphviz with ":"
            source_function_name = function.id.replace(":", "𐫵")

            # Create a node for the source function
            self.dot.node(
                name=source_function_name,
                shape="rectangle",
                fillcolor=CALLGRAPH_USER_DEFINED_FUNCTIONS_COLOR,
            )

            # Find all functions called inside source function
            for statement in function.statements:
                if isinstance(statement, SierraVariableAssignation):
                    called_function = statement.function

                user_defined_function = USER_DEFINED_FUNCTION_REGEXP.match(called_function.id)
                # Call to an user defined function
                if user_defined_function:
                    # Create a node for an user defined function
                    called_function_name = user_defined_function.group(2)
                    called_function_name = called_function_name
                    called_function_name = called_function_name.replace(":", "𐫵")
                    self.dot.node(
                        name=called_function_name,
                        shape="rectangle",
                        fillcolor=CALLGRAPH_USER_DEFINED_FUNCTIONS_COLOR,
                    )

                # Call to a libfunc function
                else:
                    # Create a node for a libfunc
                    called_function_name = called_function.id
                    called_function_name = called_function_name
                    called_function_name = called_function_name.replace(":", "𐫵")
                    self.dot.node(
                        name=called_function_name, shape="oval", fillcolor=CALLGRAPH_LIBFUNCS_COLOR
                    )

                # Create an edge between the source function and the called function
                self.dot.edge(
                    source_function_name,
                    called_function_name,
                )

    def _print_callgraph(self) -> None:
        """
        Render the dot call-graph
        """
        self.dot.render(view=True)
