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
        self.variable_name = variable_name
        self.is_set = False
        self.used_in_condition = False
        self.used_in_branch = True
        self.instance = Variable.counter if self.is_set else None
        self.versions = 1

    def set(self) -> None:
        """
        A variable is set when it's accessed
        """
        self.is_set = True
        self.instance = Variable.counter
        Variable.counter += 1

    def name(self, value) -> str:
        """
        Return the variable name
        Either a custom name (function arguments/return value) or v_<n> by default
        """
        if not self.used_in_condition:
            self.used_in_condition = True

        if not self.used_in_branch:
            self.versions += 1
            self.used_in_branch = True

        if not self.is_set:
            self.set()

        # If the variable has a name
        if self.variable_name is not None:
            return self.variable_name

        if value == True and self.versions != 1:
            # Phi function
            versions_names = ", ".join(
                ["Var%s_%s" % (self.instance, version) for version in range(1, self.versions + 1)]
            )
            name = f"Φ({versions_names})"
        else:
            # Use default name (Var<n>)
            name = "Var%s_%s" % (self.instance, self.versions)
        return name
