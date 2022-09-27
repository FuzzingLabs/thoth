from typing import Optional, Tuple
from thoth.app.decompiler.variable import Variable


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

    def new_function_init(self) -> None:
        """
        Initialize AP and FP at the beginning of a function
        """
        self.ap_position += 1
        self.fp_position = self.ap_position

    def new_if_branch(self) -> None:
        """
        Create a backup of the stack size at the beginning of an if branch
        """
        if len(self.stack_size_backup) != 0:
            for i in range(self.stack_size_backup[-1], len(self.memory)):
                self.memory[i].used_in_condition = False
        self.stack_size_backup.append(len(self.memory))

    def end_if_branch(self) -> None:
        """
        Restore stack size
        """
        self.stack_size_backup.pop()
        self.ap_position = len(self.memory)

    def new_else_branch(self) -> None:
        """
        Move AP at the same level as at the beginning of the if branch
        """
        self.ap_position = len(self.memory) - (len(self.memory) - self.stack_size_backup[-1])
        for i in range(self.stack_size_backup[-1], len(self.memory)):
            self.memory[i].used_in_condition = False

    def new_variable(self, variable_name: Optional[str] = None) -> None:
        """
        Create a new variable in memory
        """
        variable = Variable(variable_name=variable_name)
        self.memory.append(variable)

    def get_variable(self, register: str, offset: int) -> Tuple[bool, Variable, bool]:
        """
        Get a variable name given a register and an offset
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
        used_in_condition = self.memory[position].used_in_condition
        name = self.memory[position].name
        return (new_variable, name, used_in_condition)
