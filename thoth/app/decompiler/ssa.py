from typing import Optional, Tuple
from thoth.app.decompiler.variable import Variable
from thoth.app.disassembler.function import Function


class SSA:
    """
    Decompiler SSA
    """

    def __init__(self) -> None:
        """
        Initialize the registers values and memory/stack
        """
        self.memory = []
        self.ap_position = 0
        self.fp_position = self.ap_position
        self.stack_size_backup = []

    def new_function_init(self, function: Function) -> None:
        """
        Initialize AP and FP at the beginning of a function
        Reference : https://eprint.iacr.org/2021/1063.pdf page 38 / Section 6.1 - Function call stack
        """
        arguments = function.arguments_list()
        # [fp - 3], [fp - 4], ...
        for argument in arguments:
            self.new_variable(variable_name=argument, function=function)
            self.ap_position += 1
        # [fp - 2]
        self.new_variable(variable_name="[callers function's frame]")
        self.ap_position += 1
        # [fp - 1]
        self.new_variable(variable_name="[return instruction]")
        self.ap_position += 1

        self.fp_position = self.ap_position

    def new_variable(
        self,
        variable_name: Optional[str] = None,
        function: Function = None,
        function_result: bool = False,
    ) -> None:
        """
        Create a new variable in memory
        Args:
            variable_name (Optional String): name of the variable
        """
        variable = Variable(
            variable_name=variable_name, function=function, function_result=function_result
        )
        self.memory.append(variable)

    def get_variable(self, register: str, offset: int) -> Tuple[bool, Variable, bool]:
        """
        Get a variable name given a register and an offset
        Args:
            register (String): "ap" of "fp"
            offset: (int): offset
        """
        new_variable = False

        # AP
        if register == "ap":
            position = self.ap_position + offset
        # FP
        else:
            position = self.fp_position + offset

        # Create a new variable
        if position == len(self.memory):
            self.new_variable()
            new_variable = True

        # Pad intermediate values with unset variables
        # And create a new variable
        elif position > len(self.memory):
            for i in range(len(self.memory), position + 1):
                self.new_variable()
                new_variable = True

        name = self.memory[position].name
        return (new_variable, name, self.memory[position])
