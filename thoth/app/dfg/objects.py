from typing import List

from thoth.app.decompiler.variable import Variable
from thoth.app.disassembler.function import Function


class DFGVariableBlock:
    """
    DFG Variable block class
    """

    def __init__(self, name: str, function: Function, is_function_argument: bool) -> None:
        self.name = name
        self.graph_representation_name = None
        self.function = function
        self.is_function_argument = is_function_argument
        self.tainting_coefficient = 0
        self.parents_blocks: List[DFGVariableBlock] = []
        self.children_blocks: List[DFGVariableBlock] = []


class DFGConstantBlock:
    """
    DFG Constant block class
    """

    def __init__(
        self, value: str, position: int, related_variable: Variable, function: Function
    ) -> None:
        self.value = value
        self.position = position
        self.graph_representation_name = "%s_%s" % (self.value, self.position)
        self.related_variable = related_variable
        self.function = function


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
