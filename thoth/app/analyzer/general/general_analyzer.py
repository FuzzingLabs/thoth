from thoth.app.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)


class GeneralAnalyzer(AbstractAnalyzer):
    """
    Contract general informations
    """

    NAME = "General"
    ARGUMENT = "general"
    HELP = "Contract general informations"
    IMPACT: ImpactClassification = ImpactClassification.NONE
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    CATEGORY: CategoryClassification = CategoryClassification.INFORMATIONAL

    def _detect(self) -> None:
        self.detected = True

        # Statistics
        functions_count = len(self.disassembler.functions)
        builtins_count = len(self.disassembler.builtins)
        structs_count = len(self.disassembler.structs)
        calls_count = 0

        entry_points = []

        for function in self.disassembler.functions:
            if function.entry_point:
                entry_points.append(function.name)
            for instruction in function.instructions:
                if instruction.opcode == "CALL":
                    calls_count += 1

        self.result.append("functions : %s" % str(functions_count))
        self.result.append("builtins : %s" % str(builtins_count))
        self.result.append("structs : %s" % str(structs_count))
        self.result.append("calls : %s" % str(calls_count))
        self.result.append("Entry points : %s" % ", ".join(entry_points))
