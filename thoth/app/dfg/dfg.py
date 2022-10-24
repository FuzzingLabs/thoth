import graphviz
from typing import List
from thoth.app.decompiler.variable import Operand, OperandType, Variable
from thoth.app.disassembler.function import Function


class DFGVariableBlock:
    """
    DFG Variable block class
    """

    def __init__(self, name: str, function: Function, is_function_argument: bool) -> None:
        self.name = name
        self.function = function
        self.is_function_argument = is_function_argument


class DFGEdge:
    """
    DFG Edge class
    """

    def __init__(
        self, source: DFGVariableBlock, destination: DFGVariableBlock, function: Function
    ) -> None:
        self.source = source
        self.destination = destination
        self.function = function


class DFG:
    """
    DataFlow Graph class
    """

    def __init__(self, variables: List[Variable]) -> None:
        self.variables = variables
        self.variables_blocks: List[DFGVariableBlock] = []
        self.edges: List[DFGEdge] = []

    def _create_blocks(self) -> None:
        """
        Create the DFG blocks from the variables
        """
        for variable in self.variables:
            variable_name = variable.name
            variable_function = variable.function
            is_function_argument = False

            if variable_function is not None:
                function_arguments = variable.function.arguments_list(implicit=False, ret=False)
                is_function_argument = variable_name in function_arguments
                # Create block
                self.variables_blocks.append(
                    DFGVariableBlock(variable_name, variable_function, is_function_argument)
                )

    def _create_edges(self) -> None:
        """
        Create the DFG edges from the variables
        """
        for variable in self.variables:
            if variable.value is None:
                continue

            destination_block = [
                b
                for b in self.variables_blocks
                if variable.function == b.function and variable.name == b.name
            ][0]

            # Source variables
            parents_variables = [v for v in variable.value.operation if isinstance(v, Operand)]
            parents_variables = [v for v in parents_variables if v.type == OperandType.VARIABLE]

            source_blocks = []
            for parent_variable in parents_variables:
                if isinstance(parent_variable.value, list):
                    source_blocks = [
                        b
                        for b in self.variables_blocks
                        if variable.function == b.function and b.name in parent_variable.value
                    ]
                else:
                    source_blocks = [
                        b
                        for b in self.variables_blocks
                        if variable.function == b.function and b.name == variable.name
                    ]

            for source_block in source_blocks:
                self.edges.append(DFGEdge(source_block, destination_block, variable.function))

    def _create_dfg(self) -> None:
        """
        Create the DFG (Blocks and Edges)
        """
        self._create_blocks()
        self._create_edges()

    def _print_dfg(self) -> str:
        """
        Generate a graph layout in Dot
        """
        self._create_dfg()

        dot = graphviz.Digraph("DataFlow Graph", comment="")
        contract_functions = list(set([v.function.name for v in self.variables_blocks]))

        # Create one subgraph per function
        subgraphs = []
        for function in contract_functions:
            subgraph = graphviz.Digraph(name=function, comment=function)
            subgraphs.append(subgraph)

        # Nodes
        for variable in self.variables_blocks:
            function_subgraph = [s for s in subgraphs if s.name == variable.function.name][0]
            function_subgraph.node(variable.name)

        # Edges
        for edge in self.edges:
            function_subgraph = [s for s in subgraphs if s.name == edge.function.name][0]
            function_subgraph.edge(edge.source.name, edge.destination.name)

        # Join subgraphs
        [dot.subgraph(_) for _ in subgraphs]

        return dot.source
