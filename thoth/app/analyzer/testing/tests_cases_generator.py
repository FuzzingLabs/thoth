from thoth.app.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
    colors,
)
from thoth.app.decompiler.decompiler import Decompiler
from thoth.app.symbex.symbex import SymbolicExecution
from thoth.app.utils import bcolors


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

        path_color = colors.HEADER if self.color else ""
        variable_color = colors.CYAN if self.color else ""

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

            paths_count = 0
            for test_case in test_cases:
                function_test_cases += "\n    "
                function_test_cases += "%sPath %s%s : " % (path_color , paths_count, colors.ENDC)
                function_test_cases += ", ".join(["%s%s%s: %s" % (variable_color, arg[0], colors.ENDC, arg[1]) for arg in test_case])
                paths_count += 1
            self.result.append(function_test_cases)

        return self.detected
