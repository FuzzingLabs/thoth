from typing import List
from lark.tree import Tree


from sierra.objects.objects import (
    SierraConditionalBranch,
    SierraFunction,
    SierraLibFunc,
    SierraReturn,
    SierraType,
    SierraVariableAssignation,
)


def _handle_type_definition(self, type_definition: Tree) -> None:
    """
    Handle sierra type definition
    """
    # Parse the type id
    concrete_type_id = list(type_definition.find_data("concrete_type_id"))
    type_name = self.reconstructor.reconstruct(concrete_type_id[-1])

    # Parse the long type id
    concrete_type_long_id = list(type_definition.find_data("concrete_type_long_id"))
    long_type_name = self.reconstructor.reconstruct(concrete_type_long_id[-1])

    sierra_type = SierraType(id=type_name, long_id=long_type_name)
    self.types.append(sierra_type)


def _handle_libfunc_definition(self, libfunc_definition: Tree) -> None:
    """
    Handle sierra libfunc definition
    """
    # Parse the libfunc id
    concrete_libfunc_id = list(libfunc_definition.find_data("concrete_libfunc_id"))[0]
    libfunc_id = self.reconstructor.reconstruct(concrete_libfunc_id)

    # Parse the libfunc long id
    concrete_libfunc_long_id = list(libfunc_definition.find_data("concrete_libfunc_long_id"))[0]
    libfunc_name = self.reconstructor.reconstruct(concrete_libfunc_long_id)

    libfunc = SierraLibFunc(id=libfunc_id, name=libfunc_name)
    self.libfuncs.append(libfunc)


def _handle_variable_assignation(self, statement: Tree) -> SierraVariableAssignation:
    """
    Handle sierra variable assignation statement
    """
    # Raw statement is the statement string as defined in the sierra source
    raw_statement = self.reconstructor.reconstruct(statement)

    # Parse function ID
    libfunc_id_tree = list(statement.find_data("concrete_libfunc_id"))[0]
    libfunc_id = self.reconstructor.reconstruct(libfunc_id_tree)
    libfunc = self._get_libfunc_by_id(id=libfunc_id)

    # Parse function arguments IDs
    function_arguments = []
    function_arguments_trees = list(list(statement.find_data("var_ids"))[0].find_data("big_int"))
    for function_argument_tree in function_arguments_trees:
        function_argument = self._get_variable_by_name(
            name=function_argument_tree.children[0].value
        )
        function_arguments.append(function_argument)

    # Parse assigned variables IDs
    assigned_variables = []
    assigned_variables_trees = list(list(statement.find_data("var_ids"))[1].find_data("big_int"))
    for assigned_variable_tree in assigned_variables_trees:
        assigned_variable = self._get_variable_by_name(
            name=assigned_variable_tree.children[0].value
        )
        assigned_variables.append(assigned_variable)

    variable_assignation = SierraVariableAssignation(
        function=libfunc,
        function_arguments=function_arguments,
        assigned_variables=assigned_variables,
        raw_statement=raw_statement,
    )

    return variable_assignation


def _handle_fallthrough(self, statement: Tree) -> SierraConditionalBranch:
    """
    Parse sierra fallthrough statement
    """
    # Raw statement is the statement string as defined in the sierra source
    raw_statement = self.reconstructor.reconstruct(statement)

    # Parse libfunc command ID
    libfunc_command_id_tree = list(statement.find_data("concrete_libfunc_id"))[0]
    libfunc_command_id = self.reconstructor.reconstruct(libfunc_command_id_tree)

    # Fallthrough offset
    fallthrough_offset_trees = int(
        list(list(statement.find_data("statement_idx"))[0].find_data("big_int"))[0]
        .children[0]
        .value
    )

    function_arguments = []
    function_arguments_trees = list(list(statement.find_data("var_ids"))[2].find_data("var_id"))
    for function_argument_tree in function_arguments_trees:
        function_argument = self.reconstructor.reconstruct(function_argument_tree)
        function_argument_variable = self._get_variable_by_name(name=function_argument)
        function_arguments.append(function_argument_variable)

    # Fallthrough arguments
    fallthrough_arguments = []
    fallthrough_arguments_trees = list(list(statement.find_data("var_ids"))[1].find_data("big_int"))
    for fallthrough_argument_tree in fallthrough_arguments_trees:
        fallthrough_arguments.append(fallthrough_argument_tree.children[0].value)

    fallthrough = SierraConditionalBranch(
        fallthrough=True,
        function=libfunc_command_id,
        parameters=function_arguments,
        edge_1_offset=fallthrough_offset_trees,
        raw_statement=raw_statement,
    )

    return fallthrough


def _handle_control_flow_command(self, statement: Tree) -> SierraConditionalBranch:
    """
    Parse sierra control flow command statement
    """
    # Raw statement is the statement string as defined in the sierra source
    raw_statement = self.reconstructor.reconstruct(statement)

    # Parse libfunc command ID
    libfunc_command_id_tree = list(statement.find_data("concrete_libfunc_id"))[0]
    libfunc_command_id = self.reconstructor.reconstruct(libfunc_command_id_tree)

    statement_idx = list(statement.find_data("statement_idx"))
    # Jump
    if len(statement_idx) == 1:
        jump_offset = int(list(statement_idx[0].find_data("big_int"))[0].children[0].value)
        control_flow_command = SierraConditionalBranch(
            function=libfunc_command_id,
            parameters=[],
            edge_1_offset=jump_offset,
            edge_2_offset=None,
            raw_statement=raw_statement,
        )
    # JNZ
    else:
        jump_offset_1 = int(list(statement_idx[0].find_data("big_int"))[0].children[0].value)
        jump_offset_2 = int(list(statement_idx[1].find_data("big_int"))[0].children[0].value) - 1

        function_arguments = []
        function_arguments_trees = list(list(statement.find_data("var_ids"))[2].find_data("var_id"))
        for function_argument_tree in function_arguments_trees:
            function_argument = self.reconstructor.reconstruct(function_argument_tree)
            function_argument_variable = self._get_variable_by_name(name=function_argument)
            function_arguments.append(function_argument_variable)

        control_flow_command = SierraConditionalBranch(
            function=libfunc_command_id,
            parameters=function_arguments,
            edge_1_offset=jump_offset_1,
            edge_2_offset=jump_offset_2,
            raw_statement=raw_statement,
        )

    return control_flow_command


def _handle_return(self, statement: Tree) -> SierraReturn:
    """
    Handle sierra return statement
    """
    # Raw statement is the statement string as defined in the sierra source
    raw_statement = self.reconstructor.reconstruct(statement)

    # Parse return values
    return_values = []
    return_values_trees = list(statement.find_data("big_int"))
    for return_value_tree in return_values_trees:
        return_variable = self._get_variable_by_name(name=return_value_tree.children[0].value)
        return_values.append(return_variable)

    return_statement = SierraReturn(variables=return_values, raw_statement=raw_statement)
    return return_statement


def _handle_statement(self, statement: Tree) -> None:
    """
    Handle sierra statement definition
    """
    # Invocation
    invocation = list(statement.find_data("invocation"))
    if invocation:
        is_assignation = bool(list(statement.find_data("assignation_operator")))

        # Variable assignation
        # <libfunc id>(<argument>) -> <assigned variables>
        if is_assignation:
            statement = self._handle_variable_assignation(statement)

        # Control flow command
        else:
            # Parse control-flow command arguments IDs
            is_fallthrough = bool(list(statement.find_data("fallthrough")))
            # <libfunc id>(<variables ids>) { fallthrough()  }
            if is_fallthrough:
                statement = self._handle_fallthrough(statement)
            # <libfunc id>(<variables ids>) { <statement offset>() <statement offset>() }
            else:
                statement = self._handle_control_flow_command(statement)

    # Return statements
    # return(<variables>)
    else:
        statement = self._handle_return(statement)

    self.statements.append(statement)


def _handle_function_declaration(self, function_declaration: Tree) -> None:
    """
    Handle sierra function definition
    """
    # Parse function id
    function_id_tree = list(function_declaration.find_data("function_id"))
    function_id = self.reconstructor.reconstruct(function_id_tree[-1])

    # Parse function start offset
    start_statement_id = list(function_declaration.find_data("statement_idx"))
    start_offset = int(self.reconstructor.reconstruct(start_statement_id[-1]))

    # Parse function parameters
    parameters = []
    parameters_tree = list(function_declaration.find_data("param"))
    for parameter_tree in parameters_tree:
        # Parameter variable id
        parameter_variable_name = self.reconstructor.reconstruct(
            list(parameter_tree.find_data("var_id"))[0]
        )[1:-1]
        parameter_type_id = self.reconstructor.reconstruct(
            list(parameter_tree.find_data("concrete_type_id"))[0]
        )
        # Parameter type
        parameter_type = self._get_type_by_id(parameter_type_id)
        parameter_variable = self._get_variable_by_name(
            name=parameter_variable_name, type=parameter_type
        )
        parameters.append(parameter_variable)

    # Parse return values
    return_values_types: List[SierraType] = []
    return_values_trees = list(
        list(function_declaration.find_data("concrete_type_ids"))[0].find_data("concrete_type_id")
    )[1:]
    for return_value_tree in return_values_trees:
        return_value_type_id = self.reconstructor.reconstruct(return_value_tree)
        return_value_type = self._get_type_by_id(return_value_type_id)
        return_values_types.append(return_value_type)

    sierra_function = SierraFunction(
        id=function_id,
        start_offset=start_offset,
        parameters=parameters,
        return_values_types=return_values_types,
    )
    self.functions.append(sierra_function)
