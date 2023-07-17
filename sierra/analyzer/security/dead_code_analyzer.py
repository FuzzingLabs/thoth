from sierra.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)
from sierra.objects.objects import SierraConditionalBranch, SierraVariableAssignation


class DeadCodeAnalyzer(AbstractAnalyzer):
    """
    Detect dead code
    """

    NAME = "Dead code"
    ARGUMENT = "dead_code"
    HELP = "Find dead code"
    IMPACT: ImpactClassification = ImpactClassification.LOW
    PRECISION: PrecisionClassification = PrecisionClassification.MEDIUM
    CATEGORY: CategoryClassification = CategoryClassification.OPTIMIZATION

    def _detect(self) -> bool:
        # User defined functions names
        functions_call_counter = {f.id: 0 for f in self.program.functions}

        # All the program statements
        statements = []
        for f in self.program.functions:
            statements += f.statements

        # Increment functions calls counters
        for statement in statements:
            if isinstance(statement, SierraVariableAssignation):
                libfunc_call = statement.function.id
            elif isinstance(statement, SierraConditionalBranch):
                libfunc_call = statement.function
            else:
                continue

            # user defined function
            if libfunc_call.startswith("function_call<user@") and libfunc_call.endswith(">"):
                # Remove function_call<> wrapper
                function_name = libfunc_call[19:-1]
                functions_call_counter[function_name] += 1

        # Find unused functions
        for function in functions_call_counter:
            if functions_call_counter[function] == 0:
                function_name = function.split("::")[-1]

                self.detected = True
                self.result.append("Function %s is never called" % function_name)

        return self.detected
