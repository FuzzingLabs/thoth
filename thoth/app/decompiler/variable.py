from typing import Optional


class Variable:
    """
    Variable class
    """

    counter = 0

    def __init__(self, variable_name: Optional[str] = None) -> None:
        """
        Initialize a new variable
        """
        Variable.counter += 1
        self.variable_name = variable_name
        self.instance = Variable.counter

    @property
    def name(self) -> str:
        """
        Return the variable name
        Either a custom name (function arguments) or v_<n> by default
        """
        # If the variable has a name
        if self.variable_name is not None:
            return self.variable_name

        # Use default name (v_<n>)
        name = "v_%s" % self.instance
        return name
