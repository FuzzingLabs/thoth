from thoth.app.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)


class FunctionsAnalyzer(AbstractAnalyzer):
    """
    Detect strings inside a contract
    """

    NAME = "Functions"
    ARGUMENT = "functions"
    HELP = "Retrieve informations about the contract's functions"
    IMPACT: ImpactClassification = ImpactClassification.NONE
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    CATEGORY: CategoryClassification = CategoryClassification.INFORMATIONAL

    def _detect(self) -> None:
        contract_functions = [
            function for function in self.disassembler.functions if not function.is_import
        ]
        self.detected = bool(contract_functions)

        for function in contract_functions:
            result = "%s" % function.name
            decorators = [decorator for decorator in function.decorators]
            if decorators:
                result += "\n"
                result += "\t- decorators : %s" % ", ".join(decorators)
            self.result.append(result)
