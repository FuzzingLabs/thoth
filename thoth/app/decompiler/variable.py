from enum import Enum
from typing import List, Optional, Union


class OperandType(Enum):
    VARIABLE = 0
    INTEGER = 1


class Operator(Enum):
    ADDITION = 0
    MULTIPLICATION = 1


class VariableValueType(Enum):
    ADDRESS = 0
    ABSOLUTE = 1
    FUNCTION_CALL = 2


class FunctionCall:
    """
    Function call class
    """

    def __init__(self, function, return_value_position: int, call_number: int) -> None:
        self.function = function
        self.return_value = self.function.arguments_list(explicit=False, implicit=False, ret=True)[
            return_value_position
        ]
        self.call_number = call_number


class Operand:
    """
    Element of an operation, either a variable/list of variables or an integer
    """

    def __init__(self, type: OperandType, value: Union[str, int, List[str], FunctionCall]) -> None:
        self.type = type
        self.value = value

    @property
    def phi_function(self) -> bool:
        """
        Check if a variable operand has several possible values
        """
        if self.type == OperandType.VARIABLE and type(self.value) is list:
            return True
        return False


class VariableValue:
    """
    Value assigned to an SSA variable
    """

    def __init__(self, type: VariableValueType, operation: List) -> None:
        self.type = type
        self.operation = operation


class Variable:
    """
    Variable class
    """

    counter = 0

    def __init__(self, variable_name: Optional[str] = None, function=None) -> None:
        """
        Initialize a new variable
        Args:
            variable_name (Optional String): the name of the variable
        """
        self.variable_name = variable_name
        self.value = None
        self.is_set = False
        self.instance = Variable.counter if self.is_set else None
        # Local or global variable
        self.local = True
        # Function where the variable is defined
        self.function = function

    def set(self) -> None:
        """
        A variable is set when it's accessed
        """
        self.is_set = True
        self.instance = Variable.counter
        Variable.counter += 1

    @property
    def name(self) -> str:
        """
        Return the variable name
        Either a custom name (function arguments/return value) or v<n> by default
        Returns:
            name (String): name of the variable
        """
        if not self.is_set:
            self.set()

        # If the variable has a name
        if self.variable_name is not None:
            return self.variable_name

        # Use default name (v_<n>)
        name = "v%s" % self.instance
        return name
