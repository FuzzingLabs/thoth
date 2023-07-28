from sierra.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)
from sierra.objects.objects import SierraConditionalBranch, SierraVariableAssignation


class UserDefinedFunctionCallAnalyzer(AbstractAnalyzer):
    """
    Detect user defined function call
    """

    NAME = "User defined function call"
    ARGUMENT = "user_defined"
    HELP = "Find user defined function calls"
    IMPACT: ImpactClassification = ImpactClassification.MEDIUM
    PRECISION: PrecisionClassification = PrecisionClassification.MEDIUM
    CATEGORY: CategoryClassification = CategoryClassification.OPTIMIZATION

    def _detect(self) -> bool:
        for f in self.program.functions:
            statements = f.statements

            for statement in statements:
                if isinstance(statement, SierraVariableAssignation):
                    libfunc_call = statement.function.id
                elif isinstance(statement, SierraConditionalBranch):
                    libfunc_call = statement.function
                else:
                    continue

                # user defined function
                if libfunc_call.startswith("function_call<user@") and libfunc_call.endswith(">"):
                    # Core functions
                    if libfunc_call.startswith("function_call<user@core"):
                        continue

                    # Remove function_call<> wrapper
                    function_name = libfunc_call[19:-1]

                    self.detected = True
                    self.result.append(
                        "User defined function %s called in %s"
                        % (function_name.split("::")[-1], f.id.split("::")[-1])
                    )

        return self.detected
