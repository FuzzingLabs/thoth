from sierra.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)


class ReentrancyGuardsAnalyzer(AbstractAnalyzer):
    """
    Detect delegate calls
    """

    NAME = "Reentrancy guards"
    ARGUMENT = "reentrancy guards"
    HELP = "Find reentrancy guards"
    IMPACT: ImpactClassification = ImpactClassification.HIGH
    PRECISION: PrecisionClassification = PrecisionClassification.MEDIUM
    CATEGORY: CategoryClassification = CategoryClassification.SECURITY

    def _detect(self) -> bool:
        program_libfuncs = self.program.libfuncs
        for program_function in program_libfuncs:
            if "reentrancy_guard" in program_function.name:
                self.detected = True
                self.result.append("This contract uses reentrancy guards")
                break

        return self.detected
