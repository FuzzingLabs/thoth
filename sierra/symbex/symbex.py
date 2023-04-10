import itertools
import re

from functools import wraps
from typing import Callable, List, Optional
from z3 import *

from sierra.objects.objects import (
    SierraBasicBlock,
    SierraFunction,
    SierraVariableAssignation,
)


class SierraSymbolicExecution:
    """
    Symbolic execution class
    """

    def __init__(self, function: SierraFunction) -> None:
        self.function = function
        self.paths = function.cfg.paths()

        # Z3 Part
        self.solver = Solver()
        self.z3_variables: List[BitVec] = []

        # All the function resolvers
        # TODO: Automatically add them using a decorator
        self.functions_resolvers: List[Callable] = [
            self.felt_const,
            self.felt_sub,
            self.felt_add,
            self.felt_div,
            self.felt_mul,
            self.storetemp,
            self.dup,
            self.rename,
        ]

    def solve(self, constraints: List[str], solves: List[str], variables_values: List[str]) -> None:
        """
        Solve the constraints using Z3
        """

        # Parse the variables and constraints defined with the CLI arguments
        variable_regexp = re.compile("v\d{1,4}")
        variable_value_regexp = re.compile("(v\d{1,4}(_\w+)?)=(\d+)")
        constraint_regexp = re.compile(
            "(v\d{1,4}(_\w+)?)((==)|(!=)|(>=)|(>)|(<=)|(<))((\d+)|(v\d{1,4}))"
        )
        solve_regexp = re.compile("(v\d{1,4}(_\w+)?)")

        # Constraints defined in the CLI arguments
        constraints_list = []
        for constraint in constraints:
            constraints_list.append(re.findall(constraint_regexp, constraint))
        constraints_variables_names = [v[0][0] for v in constraints_list]

        # Variables defined in the CLI arguments
        variables_values_list = []
        for variable in variables_values:
            variables_values_list.append(re.findall(variable_value_regexp, variable))
        variables_values_names = [v[0][0] for v in variables_values_list]

        # Variables values to solve defined in the CLI arguments
        solve_values_list = []
        for solve in solves:
            solve_values_list.append(re.findall(solve_regexp, solve))
        solves_values_names = [v[0][0] for v in solve_values_list]

        for path in self.paths:
            # Initialize solver for each napth
            self.solver = z3.Solver()
            self.z3_variables = []

            # Load variables into z3
            self._load_path_variables(path)

            if not set(constraints_variables_names) <= set([str(_) for _ in self.z3_variables]):
                continue

            # Load variables values defined in CLI into Z3
            for variable in variables_values_list:
                try:
                    variable_name = [v for v in self.z3_variables if str(v) == variable[0][0]][0]
                    self.solver.add(variable_name == int(variable[0][2]))
                except:
                    pass

            # Load constraints defined in CLI into Z3
            for constraint in constraints_list:
                try:
                    variable_name = [v for v in self.z3_variables if str(v) == constraint[0][0]][0]

                    # Constraint with an integer
                    if constraint[0][10]:
                        right_side_expression = int(constraint[0][10])
                    # Constraint with another variable
                    else:
                        right_side_expression = [
                            v for v in self.z3_variables if str(v) == constraint[0][11]
                        ][0]

                    # Equality constraint
                    if constraint[0][2] == "==":
                        self.solver.add(variable_name == right_side_expression)
                    # Inequality constraint
                    elif constraint[0][2] == "!=":
                        self.solver.add(variable_name != right_side_expression)
                    # Superior constraint
                    elif constraint[0][2] == ">":
                        self.solver.add(variable_name > right_side_expression)
                    # Superior or equal constraint
                    elif constraint[0][2] == ">=":
                        self.solver.add(variable_name >= right_side_expression)
                    # Inferior constraint
                    elif constraint[0][2] == "<":
                        self.solver.add(variable_name < right_side_expression)
                    # Inferior or equal constraint
                    elif constraint[0][2] == "<=":
                        self.solver.add(variable_name <= right_side_expression)
                except:
                    continue

            # Solve the constraints
            if self.solver.check() == z3.sat:
                model = self.solver.model()

                # Create a dict from the z3 model
                dict_model = {}
                for d in self.solver.model():
                    dict_model[str(d)] = model[d]

                # Format the result
                result = [(k, v) for k, v in dict_model.items() if k in solves_values_names]
                result = sorted(result)
                return result
        return []

    def _load_path_variables(self, basic_blocks: List[SierraBasicBlock]) -> None:
        """
        Load path variables into z3
        """

        # Load function arguments into z3 variables
        self.z3_variables += [BitVec(p.representation_name, 32) for p in self.function.parameters]

        # All the path statements
        statements = list(itertools.chain.from_iterable([b.statements for b in basic_blocks]))

        # Load the variables assignations into z3
        for statement in statements:
            if isinstance(statement, SierraVariableAssignation):
                self.z3_variables += [
                    BitVec(v.representation_name, 32) for v in statement.assigned_variables
                ]
                self._variable_assignation_to_z3(statement)

    def _function_arguments_to_z3(self, function: SierraFunction):
        """
        Create Z3 variables from Sierra function arguments
        """

        for parameter in function.parameters:
            self.z3_variables.append(BitVec(parameter.representation_name, 32))

    def _variable_assignation_to_z3(self, variable_assignation: SierraVariableAssignation):
        """
        Transform a Sierra variable assignation to a z3 constraint
        """

        # z3 assigned variables
        assigned_variables = []
        assigned_variables_names = [v for v in variable_assignation.assigned_variables]
        for v in assigned_variables_names:
            assigned_variables.append(
                [_ for _ in self.z3_variables if v.representation_name == str(_)][0]
            )

        # z3 function arguments
        function_arguments = []
        function_arguments_names = [v for v in variable_assignation.libfunc_arguments]
        for v in function_arguments_names:
            function_arguments += [_ for _ in self.z3_variables if v.representation_name == str(_)][
                :1
            ]

        # Resolve function
        function_name = variable_assignation.function.name

        for resolver in self.functions_resolvers:
            variable_value = resolver(
                function_name=function_name,
                assigned_variables=assigned_variables,
                function_arguments=function_arguments,
            )
            if variable_value is not None:
                self.solver.add(variable_value)
                break

    def felt_const(
        self,
        function_name: str,
        assigned_variables: List[z3.z3.BitVecRef],
        function_arguments: List[z3.z3.BitVecRef],
    ) -> Optional[z3.z3.BoolRef]:
        """
        Convert felt_const function call to a Z3 constraint
        """
        function_regexp = r"felt(252)?_const<([0-9]+)>"

        match_function = re.match(function_regexp, function_name)
        if match_function is None:
            return None

        variable = assigned_variables[0]
        const_value = int(match_function.group(2))

        return self.solver.add(variable == const_value)

    def felt_sub(
        self,
        function_name: str,
        assigned_variables: List[z3.z3.BitVecRef],
        function_arguments: List[z3.z3.BitVecRef],
    ) -> Optional[z3.z3.BoolRef]:
        """
        Convert felt_sub function call to a Z3 constraint
        """
        function_regexp = r"felt(252)?_sub"

        if not re.match(function_regexp, function_name):
            return None

        variable = assigned_variables[0]

        return self.solver.add(variable == function_arguments[0] - function_arguments[1])

    def felt_div(
        self,
        function_name: str,
        assigned_variables: List[z3.z3.BitVecRef],
        function_arguments: List[z3.z3.BitVecRef],
    ) -> Optional[z3.z3.BoolRef]:
        """
        Convert felt_div function call to a Z3 constraint
        """
        function_regexp = r"felt(252)?_div"

        if not re.match(function_regexp, function_name):
            return None

        variable = assigned_variables[0]

        return self.solver.add(variable == function_arguments[0] / function_arguments[1])

    def felt_mul(
        self,
        function_name: str,
        assigned_variables: List[z3.z3.BitVecRef],
        function_arguments: List[z3.z3.BitVecRef],
    ) -> Optional[z3.z3.BoolRef]:
        """
        Convert felt_mul function call to a Z3 constraint
        """
        function_regexp = r"felt(252)?_mul"

        if not re.match(function_regexp, function_name):
            return None

        variable = assigned_variables[0]

        return self.solver.add(variable == function_arguments[0] / function_arguments[1])

    def felt_add(
        self,
        function_name: str,
        assigned_variables: List[z3.z3.BitVecRef],
        function_arguments: List[z3.z3.BitVecRef],
    ) -> Optional[z3.z3.BoolRef]:
        """
        Convert felt_add function call to a Z3 constraint
        """
        function_regexp = r"felt(252)?_add"

        if not re.match(function_regexp, function_name):
            return None

        variable = assigned_variables[0]
        return self.solver.add(variable == function_arguments[0] + function_arguments[1])

    def storetemp(
        self,
        function_name: str,
        assigned_variables: List[z3.z3.BitVecRef],
        function_arguments: List[z3.z3.BitVecRef],
    ) -> Optional[z3.z3.BoolRef]:
        """
        Convert store_temp function call to a Z3 constraint
        """

        if not function_name.startswith("store_temp"):
            return None

        variable = assigned_variables[0]
        return self.solver.add(variable == function_arguments[0])

    def dup(
        self,
        function_name: str,
        assigned_variables: List[z3.z3.BitVecRef],
        function_arguments: List[z3.z3.BitVecRef],
    ) -> Optional[z3.z3.BoolRef]:
        """
        Convert dup function call to a Z3 constraint
        """

        if not function_name.startswith("dup"):
            return None

        variable = assigned_variables[1]
        return self.solver.add(variable == function_arguments[0])

    def rename(
        self,
        function_name: str,
        assigned_variables: List[z3.z3.BitVecRef],
        function_arguments: List[z3.z3.BitVecRef],
    ) -> Optional[z3.z3.BoolRef]:
        """
        Convert rename function call to a Z3 constraint
        """

        if not function_name.startswith("rename"):
            return None

        variable = assigned_variables[0]
        return self.solver.add(variable == function_arguments[0])
