from typing import Optional


class Variable:
    """
    Variable class
    """

    counter = 0

    def __init__(self, variable_name: Optional[str] = None) -> None:
        """
        Initialize a new variable
        Args:
            variable_name (Optional String): the name of the variable
        """
        self.variable_name = variable_name
        self.is_set = False
        self.instance = Variable.counter if self.is_set else None

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
