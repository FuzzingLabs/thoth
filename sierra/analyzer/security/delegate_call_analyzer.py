from sierra.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)


class DelegateCallAnalyzer(AbstractAnalyzer):
    """
    Detect delegate calls
    """

    NAME = "Delegate call"
    ARGUMENT = "delegate_call"
    HELP = "Find delegate calls"
    IMPACT: ImpactClassification = ImpactClassification.MEDIUM
    PRECISION: PrecisionClassification = PrecisionClassification.MEDIUM
    CATEGORY: CategoryClassification = CategoryClassification.SECURITY

    def _detect(self) -> bool:
        program_libfuncs = self.program.libfuncs
        for program_function in program_libfuncs:
            if program_function.name == "library_call_syscall":
                self.detected = True
                self.result.append("This contract uses library_call_syscall function")
                break

        return self.detected
