from sierra.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)
from sierra.objects.objects import SierraConditionalBranch, SierraVariableAssignation


class UnusedArgumentsAnalyzer(AbstractAnalyzer):
    """
    Detect dead code
    """

    NAME = "Unused arguments"
    ARGUMENT = "unused_arguments"
    HELP = "Unused arguments"
    IMPACT: ImpactClassification = ImpactClassification.LOW
    PRECISION: PrecisionClassification = PrecisionClassification.MEDIUM
    CATEGORY: CategoryClassification = CategoryClassification.OPTIMIZATION

    def _detect(self) -> bool:
        for function in self.program.functions:
            # Function arguments usage counter
            function_arguments_counter = {a.representation_name: 0 for a in function.parameters}

            for statement in function.statements:
                if isinstance(statement, SierraVariableAssignation):
                    function_arguments = [
                        a.representation_name for a in statement.libfunc_arguments
                    ]
                elif isinstance(statement, SierraConditionalBranch):
                    function_arguments = [a.representation_name for a in statement.parameters]
                else:
                    continue

                # Increment arguments usage counter
                for argument in function_arguments:
                    try:
                        function_arguments_counter[argument] += 1
                    except:
                        pass

            # Find unused arguments
            for argument in function_arguments_counter:
                if function_arguments_counter[argument] == 0:
                    function_name = function.id.split("::")[-1]

                    self.detected = True
                    self.result.append(
                        "Argument %s is never user in function %s" % (argument, function_name)
                    )

        return self.detected
