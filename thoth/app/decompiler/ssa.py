from typing import Optional
from thoth.app.decompiler.variable import Variable


class SSA:
    """
    Decompiler SSA
    """

    def __init__(self):
        """
        Initialize the registers values and memory
        """
        self.memory = []
        self.ap_position = 0
        self.fp_position = self.ap_position

    def new_function_init(self):
        """
        When a function starts, fp is equal to ap
        """
        self.fp_position = self.ap_position + 1

    def new_variable(self, variable_name: Optional[str] = None) -> None:
        """
        Create a new variable in memory
        """
        self.ap_position += 1
        v = Variable(variable_name=variable_name)
        self.memory.append(v)

    def get_variable(self, register: str, offset: int) -> Variable:
        """
        Get a variable name given a register and an offset
        """
        if register == "ap":
            position = self.ap_position + offset
        else:
            position = self.fp_position + offset

        # Create a new variable
        if position == len(self.memory):
            v = Variable()
            self.memory.append(v)

        # Pad intermediate values with unset variables
        elif position > len(self.memory):
            for i in range(len(self.memory), position + 1):
                v = Variable()
                self.memory.append(v)
        return self.memory[position].name
