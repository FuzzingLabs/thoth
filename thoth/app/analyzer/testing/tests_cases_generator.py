from thoth.app.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)
from thoth.app.decompiler.decompiler import Decompiler
from thoth.app.symbex.symbex import SymbolicExecution


class TestCasesGeneratorAnalyzer(AbstractAnalyzer):
    """
    Detect strings inside a contract
    """

    NAME = "Tests cases generator"
    ARGUMENT = "tests"
    HELP = "Automatically generate test cases for each function of the contract"
    IMPACT: ImpactClassification = ImpactClassification.INFORMATIONAL
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    CATEGORY: CategoryClassification = CategoryClassification.ANALYTICS

    def _detect(self) -> bool:
        self.detected = True

        contract_functions = self.disassembler.functions
        decompiler = Decompiler(functions=contract_functions)
        decompiler.decompile_code(first_pass_only=True)

        symbex = SymbolicExecution(decompiler.ssa.memory)

        for function in contract_functions:
            if function.is_import:
                continue

            test_cases = symbex._generate_test_cases(function=function)
            if not test_cases:
                continue

            function_test_cases = "%s" % function.name

            for test_case in test_cases:
                function_test_cases += "\n    "
                function_test_cases += ", ".join(["%s: %s" % (arg[0], arg[1]) for arg in test_case])
            self.result.append(function_test_cases)

        return self.detected
