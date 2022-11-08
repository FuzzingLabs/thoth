from typing import List, Tuple
from z3 import *

from thoth.app.decompiler.variable import OperandType, Operator, Variable, VariableValueType


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
            self.z3_variables.append(Int(variable.name))

    def _create_operations(self) -> None:
        """
        Assign variables value in the z3 solver
        """
        for variable in self.variables:
            if variable.value is None:
                continue
            if variable.value.type == VariableValueType.FUNCTION_CALL:
                continue
            if variable.value.type == VariableValueType.ADDRESS:
                continue

            assigned_variable = [v for v in self.z3_variables if variable.name == str(v)][0]
            operation = variable.value.operation
            # Simple variable assignation
            if len(operation) == 1:
                if operation[0].type == OperandType.INTEGER:
                    self.solver.add(assigned_variable == int(operation[0].value))
                else:
                    assigned_variable_value = [
                        v for v in self.z3_variables if str(v) == operation[0].value[0]
                    ][0]
                    self.solver.add(assigned_variable == assigned_variable_value)

            # Assignation with an operation
            else:
                # First operand
                if operation[0].type == OperandType.INTEGER:
                    first_operand = int(operation[0].value)
                else:
                    first_operand = [
                        v for v in self.z3_variables if str(v) == operation[0].value[0]
                    ][0]

                # Second operand
                if operation[2].type == OperandType.INTEGER:
                    second_operand = int(operation[2].value)
                else:
                    second_operand = [
                        v for v in self.z3_variables if str(v) == operation[0].value[0]
                    ][0]

                # Operation
                if operation[1] == Operator.ADDITION:
                    self.solver.add(assigned_variable == first_operand + second_operand)
                else:
                    self.solver.add(assigned_variable == first_operand * second_operand)

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
        self._create_operations()
        return ()
