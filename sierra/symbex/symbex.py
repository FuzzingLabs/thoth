import itertools
import re

from typing import Callable, List, Optional
from z3 import *

from sierra.objects.objects import (
    SierraBasicBlock,
    SierraConditionalBranch,
    SierraFunction,
    SierraVariableAssignation,
)


class SierraSymbolicExecution:
    """
    Symbolic execution class
    """

    from ._functions import (
        bool_and,
        bool_or,
        bool_xor,
        dup,
        felt_add,
        felt_const,
        felt_div,
        felt_mul,
        felt_sub,
        rename,
        storetemp,
    )

    def __init__(self, function: SierraFunction) -> None:
        self.function = function
        self.paths = function.cfg.paths()

        # Z3 Part
        self.solver = Solver()
        self.z3_variables: List[BitVec] = []

        # All the function resolvers
        # TODO: Automatically add them using a decorator
        self.functions_resolvers: List[Callable] = [
            self.bool_and,
            self.bool_or,
            self.bool_xor,
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

    def solve_test_function(self) -> True:
        """
        Find if a `thoth_test` function pass all its conditions (asserts)
        """

        for path in self.paths:
            # Initialize solver for each napth
            self.solver = z3.Solver()
            self.z3_variables = []

            # Load variables into z3
            self._load_path_variables(path)

            # Load conditions into z3
            self._load_path_conditions(path)

            # Solve the constraints
            if not self.solver.check() == z3.sat:
                return (False, len(self.paths))

        return (True, len(self.paths))

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

    def _load_path_conditions(self, basic_blocks: List[SierraBasicBlock]) -> None:
        """
        Load path conditions into z3
        """

        # Load function arguments into z3 variables
        self.z3_variables += [BitVec(p.representation_name, 32) for p in self.function.parameters]

        # All the path statements
        statements = list(itertools.chain.from_iterable([b.statements for b in basic_blocks]))

        # Load the conditions
        for statement in statements:
            if (
                isinstance(statement, SierraConditionalBranch)
                and statement.edge_2_offset is not None
            ):
                function_name = statement.function
                function_arguments = [v.representation_name for v in statement.parameters]

                if function_name.endswith("is_zero"):
                    variable_name = [
                        v for v in self.z3_variables if str(v) == function_arguments[0]
                    ][0]
                    self.solver.add(variable_name == 0)

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
