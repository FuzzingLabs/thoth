import re
from thoth.app.detectors.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)


class VariableNamingAnalyzer(AbstractAnalyzer):
    """
    Detect variable names that are not in snake case
    """

    NAME = "Variable naming"
    ARGUMENT = "variables_naming"
    HELP = "Detects variable names that are not in snake case"
    IMPACT: ImpactClassification = ImpactClassification.NONE
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    CATEGORY: CategoryClassification = CategoryClassification.OPTIMIZATION

    def _detect(self) -> None:
        snake_case_regexp = r"^([a-z0-9]*_*[a-z0-9]*)*$"

        contract_functions = self.disassembler.functions

        for function in contract_functions:
            if function.is_import:
                continue

            function_arguments = []

            arguments_list = []
            for dict in (function.args, function.implicitargs):
                if dict is not None:
                    arguments_list.append(dict)

            # Get arguments names
            for argument in arguments_list:
                for _ in [*argument.values()]:
                    function_arguments.append([*_.keys()][0])

            for argument in function_arguments:
                is_snake_case = bool(re.match(snake_case_regexp, argument))
                if not is_snake_case:
                    self.detected = True
                    self.result.append(
                        "%s argument name (%s function) needs to be in snake case"
                        % (argument, function.name.split(".")[-1])
                    )
