from sierra.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)


class StatisticsAnalyzer(AbstractAnalyzer):
    """
    Contract general informations
    """

    NAME = "Statistics"
    ARGUMENT = "statistics"
    HELP = "General statistics about the contract"
    IMPACT: ImpactClassification = ImpactClassification.INFORMATIONAL
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    CATEGORY: CategoryClassification = CategoryClassification.ANALYTICS

    def _detect(self) -> bool:
        self.detected = True

        # Statistics
        functions_count = len(self.program.functions)
        builtins_count = len(self.program.libfuncs)
        types_count = len(self.program.types)

        # Format the statistics
        self.result.append("functions : %s" % str(functions_count))
        self.result.append("libfuncs : %s" % str(builtins_count))
        self.result.append("types : %s" % str(types_count))

        return self.detected
