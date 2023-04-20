from thoth.app.analyzer.abstract_analyzer import (
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
        if self.disassembler.cairo1:
            return False

        self.detected = True

        # Statistics
        functions_count = len(self.disassembler.functions)
        builtins_count = len(self.disassembler.builtins)
        structs_count = len(self.disassembler.structs)
        calls_count = 0

        # Count the calls
        for function in self.disassembler.functions:
            for instruction in function.instructions:
                if instruction.opcode == "CALL":
                    calls_count += 1

        self.result.append("functions : %s" % str(functions_count))
        self.result.append("builtins : %s" % str(builtins_count))
        self.result.append("structs : %s" % str(structs_count))
        self.result.append("calls : %s" % str(calls_count))

        return self.detected
