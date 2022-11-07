from z3 import *
from typing import Tuple
from thoth.app.disassembler.function import Function


class SymbolicExecution:
    """
    Symbolic execution class
    """

    def __init__(self, function: Function) -> None:
        self.function = function
        self.solver = z3.Solver()

    def _generate_test_cases(self) -> Tuple[Tuple[str, int]]:
        """
        Generate a list of testcases allowing to cover all the possible paths of a function
        """
        return
