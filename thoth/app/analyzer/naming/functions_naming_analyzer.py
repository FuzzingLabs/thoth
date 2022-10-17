import re
from thoth.app.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)


class FunctionNamingAnalyzer(AbstractAnalyzer):
    """
    Detect function names that are not in snake case
    """

    NAME = "Function naming"
    ARGUMENT = "function_naming"
    HELP = "Detect function names that are not in snake case"
    IMPACT: ImpactClassification = ImpactClassification.NONE
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    CATEGORY: CategoryClassification = CategoryClassification.OPTIMIZATION

    def _detect(self) -> None:
        snake_case_regexp = r"^([a-z0-9]*_*[a-z0-9]*)*$"

        contract_functions = self.disassembler.functions

        for function in contract_functions:
            function_name = function.name.split(".")[-1]
            is_snake_case = bool(re.match(snake_case_regexp, function_name))
            if not is_snake_case:
                self.detected = True
                self.result.append("%s function name needs to be in snake case" % function_name)
