from sierra.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)
from sierra.objects.objects import SierraConditionalBranch, SierraVariableAssignation


class IntegerOverflowAnalyzer(AbstractAnalyzer):
    """
    Detect integer overflow
    """

    NAME = "Integer overflow"
    ARGUMENT = "integer_overflow"
    HELP = "Detect Integer overflow"
    IMPACT: ImpactClassification = ImpactClassification.MEDIUM
    PRECISION: PrecisionClassification = PrecisionClassification.MEDIUM
    CATEGORY: CategoryClassification = CategoryClassification.SECURITY

    def _detect(self) -> bool:
        integer_overflow_functions = ["_sub", "_add", "_mul"]

        for function in self.program.functions:
            integer_overflow = False
            for statement in function.statements:
                if isinstance(statement, SierraVariableAssignation):
                    function_arguments = [
                        a.representation_name for a in statement.libfunc_arguments
                    ]
                elif isinstance(statement, SierraConditionalBranch):
                    function_arguments = [a.representation_name for a in statement.parameters]
                else:
                    continue
                
                # Detect integer overflow
                for argument in function_arguments:
                    risky_function = any(
                        [function.id.endswith(f) for f in integer_overflow_functions]
                    )
                    if argument in function_arguments:
                        integer_overflow |= risky_function

            if integer_overflow:
                self.detected = True
                self.result.append(
                    "Integer overflow detected in function %s" % function.id.split("::")[-1]
                )

        return self.detected
