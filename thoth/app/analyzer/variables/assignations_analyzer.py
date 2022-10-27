from thoth.app.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)
from thoth.app.decompiler.decompiler import Decompiler
from thoth.app.decompiler.variable import Operand, Operator, VariableValue
from thoth.app.disassembler.function import Function


def variable_value_to_str(variable_value: VariableValue, function: Function) -> str:
    """
    Convert a list of operands/operators to a string
    """
    result = ""
    function_arguments = function.arguments_list()

    for element in variable_value.operation:
        # Operator
        if not isinstance(element, Operand):
            result += " + " if element == Operator.MULTIPLICATION else " * "
            continue

        # Operand
        if not isinstance(element.value, list):
            element_value = str(element.value)
            if element_value in function_arguments:
                element_value = "f%s_%s" % (str(function.id), element_value)
            result += element_value
            continue

        if len(element.value) == 1:
            element_value = str(element.value[0])
            if element_value in function_arguments:
                element_value = "f%s_%s" % (str(function.id), element_value)
            result += element_value
            continue

        element_value = []
        for element in element.value:
            if element in function_arguments:
                element_value.append("f%s_%s" % (str(function.id), element))
            else:
                element_value.append(element)
        possibles_values = ", ".join(element_value)
        result += "Φ(%s)" % possibles_values
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
                assignation = "%s = %s" % (
                    variable.name,
                    variable_value_to_str(variable_value, variable.function),
                )
                self.result.append(assignation)
        self.detected = True
