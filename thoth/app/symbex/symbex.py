from typing import List, Tuple
from z3 import *
from thoth.app.cfg.cfg import BasicBlock

from thoth.app.decompiler.variable import OperandType, Operator, Variable, VariableValueType


class SymbolicExecution:
    """
    Symbolic execution class
    """

    def __init__(self, variables: List[Variable]) -> None:
        self.solver = z3.Solver()
        self.variables: List[Variable] = variables
        self.z3_variables: List[ArithRef] = []
        self.constraints: List[ArithRef] = []

    def _create_z3_variables(self) -> None:
        """
        Create z3 ArithRef objects from the program memory
        """
        # Init z3 variables list
        self.z3_variables = []
        for variable in self.variables:
            self.z3_variables.append(Int(variable.name))

    def _create_operations(self, variables: List[Variable]) -> None:
        """
        Assign variables value in the z3 solver
        """
        for variable in variables:
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
                    path_variables = [v.name for v in variables]
                    operand_variable_name = [o for o in operation[0].value if o in path_variables][
                        0
                    ]
                    assigned_variable_value = [
                        v for v in self.z3_variables if str(v) == operand_variable_name
                    ][0]
                    self.solver.add(assigned_variable == assigned_variable_value)

            # Assignation with an operation
            else:
                # First operand
                if operation[0].type == OperandType.INTEGER:
                    first_operand = int(operation[0].value)
                else:
                    path_variables = [v.name for v in variables]
                    operand_variable_name = [o for o in operation[0].value if o in path_variables][
                        0
                    ]
                    first_operand = [
                        v for v in self.z3_variables if str(v) == operand_variable_name
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

    def _find_paths(self, function: Function) -> List[List[BasicBlock]]:
        """
        Find all the possible paths betwwen the basic blocks in a function
        """
        paths = []

        # Find paths starting blocks
        for block in function.cfg.basicblocks:
            if len(function.cfg.parents(block)) == 0:
                paths.append([block])

        # Find all the paths
        while True:
            new_paths = []

            for i in range(len(paths)):
                last_block_children = function.cfg.children(paths[i][-1])
                for child_block in last_block_children:
                    new_paths.append(paths[i] + [child_block])
                if len(last_block_children) == 0:
                    new_paths.append(paths[i])

            # No new paths
            if new_paths == paths:
                break
            paths = new_paths
        return paths

    def _get_constraints(self, basic_blocks: List[BasicBlock]) -> List[ArithRef]:
        """
        Get the list of requiered z3 constraints to traverse a path
        """
        constraints = []

        for block in basic_blocks:
            block_edges = [edge.destination for edge in block.edges_offset]
            if not len(block_edges) == 2:
                continue

            # Find the latest defined variable in the block
            # The constraint is either <latest_defined_var> == 0 (IF branch)
            # or <latest_defined_var> != 0 (ELSE branch)
            try:
                block_last_variable = block.variables[-1]
                block_last_z3_variable = [
                    v for v in self.z3_variables if str(v) == block_last_variable.name
                ][0]
            except:
                continue

            # If branch
            if len([b for b in basic_blocks if b.start_offset == block_edges[0]]) != 1:
                constraints.append(block_last_z3_variable == 0)
            # Else branch
            elif len([b for b in basic_blocks if b.start_offset == block_edges[1]]) != 1:
                constraints.append(block_last_z3_variable != 0)
        return constraints

    def _generate_test_cases(self, function: Function) -> Tuple[Tuple[str, int]]:
        """
        Generate a list of testcases allowing to cover all the possible paths of a function
        """
        paths = self._find_paths(function)

        # Function arguments variables
        function_arguments = [
            v for v in self.variables if v.function == function and v.is_function_argument
        ]

        for path in paths:
            # Use a new solver for each path
            self.solver = z3.Solver()
            # Initialize variables
            self._create_z3_variables()

            # Load variables assignations into z3
            path_variables = []
            for block in path:
                path_variables += block.variables
            path_variables = function_arguments + path_variables
            self._create_operations(path_variables)
            constraints = self._get_constraints(path)

        return ()
