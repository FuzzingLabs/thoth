from sierra.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)
from sierra.utils import colors


class FunctionsAnalyzer(AbstractAnalyzer):
    """
    Analyze a contract functions
    """

    NAME = "Functions"
    ARGUMENT = "functions"
    HELP = "Retrieve informations about the contract's functions"
    IMPACT: ImpactClassification = ImpactClassification.INFORMATIONAL
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    CATEGORY: CategoryClassification = CategoryClassification.ANALYTICS

    def _detect(self) -> bool:
        contract_functions = self.program.functions
        self.detected = bool(contract_functions)

        if not contract_functions:
            return self.detected

        # Print the functions prototypes
        for function in contract_functions:
            self.result.append(function.prototype)

        return self.detected
