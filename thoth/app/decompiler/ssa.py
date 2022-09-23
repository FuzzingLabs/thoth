from typing import Optional
from thoth.app.decompiler.variable import Variable


class SSA:
    """
    Decompiler SSA
    """

    def __init__(self) -> None:
        """
        Initialize the registers values and memory
        """
        self.memory = []
        self.ap_position = 0
        self.fp_position = self.ap_position
        self.new_declared_variables = 0

    def new_function_init(self) -> None:
        """
        When a function starts, fp is equal to ap
        """
        self.fp_position = self.ap_position

    def new_instruction(self) -> None:
        """
        Initialize the number of new declared variables
        """
        self.new_declared_variables = 0

    def update_ap(self):
        """
        Update AP register value
        """
        self.ap_position += self.new_declared_variables

    def new_variable(self, variable_name: Optional[str] = None) -> None:
        """
        Create a new variable in memory
        """
        v = Variable(variable_name=variable_name)
        self.memory.append(v)
        self.new_declared_variables += 1

    def get_variable(self, register: str, offset: int) -> Variable:
        """
        Get a variable name given a register and an offset
        """
        # AP
        if register == "ap":
            position = self.ap_position + offset
        # FP
        else:
            position = self.fp_position + offset

        # Create a new variable
        if position == len(self.memory):
            self.new_variable()

        # Pad intermediate values with unset variables
        # And create a new variable
        elif position > len(self.memory):
            for i in range(len(self.memory), position + 1):
                self.new_variable()
        return self.memory[position].name
