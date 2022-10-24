from thoth.app.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)
from thoth.app.decompiler.decompiler import Decompiler
from thoth.app.decompiler.variable import Operand, Operator, VariableValue


def variable_value_to_str(variable_value: VariableValue) -> str:
    """
    Convert a list of operands/operators to a string
    """
    result = ""
    for element in variable_value.operation:
        if isinstance(element, Operand):
            if isinstance(element.value, list):
                if len(element.value) == 1:
                    result += str(element.value[0])
                else:
                    possibles_values = ", ".join(element.value)
                    result += "Φ(%s)" % possibles_values
            else:
                result += str(element.value)
        else:
            result += " + " if element == Operator.MULTIPLICATION else " * "
    return result


class AssignationsAnalyzer(AbstractAnalyzer):
    """
    Detect strings inside a contract
    """

    NAME = "Assignations"
    ARGUMENT = "assignations"
    HELP = "List of variables assignations"
    IMPACT: ImpactClassification = ImpactClassification.INFORMATIONAL
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    CATEGORY: CategoryClassification = CategoryClassification.OPTIMIZATION

    def _detect(self) -> None:
        contract_functions = self.disassembler.functions
        self.decompiler = Decompiler(functions=contract_functions)
        self.decompiler.decompile_code(first_pass_only=True)

        memory = self.decompiler.ssa.memory
        for variable in memory:
            variable_value = variable.value
            if variable_value is not None:
                assignation = "%s = %s" % (variable.name, variable_value_to_str(variable_value))
                self.result.append(assignation)
        self.detected = True
