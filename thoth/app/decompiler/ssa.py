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
        self.fp_position = self.ap_position

    def get_variable(self, register: str, offset: int) -> Variable:
        """
        Get a variable name given a register and an offset
        """
        if register == "ap":
            position = self.ap_position + offset
        else:
            position = self.fp_position + offset

        self.memory.append(Variable())
        return self.memory[position].name
