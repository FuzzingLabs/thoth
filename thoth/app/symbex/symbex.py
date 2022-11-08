from typing import List, Tuple
from z3 import *

from thoth.app.decompiler.variable import Variable


class SymbolicExecution:
    """
    Symbolic execution class
    """

    def __init__(self, variables: List[Variable]) -> None:
        self.solver = z3.Solver()
        self.variables: List[Variable] = variables
        self.z3_variables: List[ArithRef] = []

    def _create_z3_variables(self) -> None:
        """
        Create z3 ArithRef objects from the program memory
        """
        for variable in self.variables:
            self.z3_variables.append(variable.name)

    def _add_variable(self, name: str) -> None:
        """
        Add a variable to the global z3 variables list
        """
        self.variables.append(Int(name))

    def _generate_test_cases(self) -> Tuple[Tuple[str, int]]:
        """
        Generate a list of testcases allowing to cover all the possible paths of a function
        """
        self._create_z3_variables()
        return ()
