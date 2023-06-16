import json
import pprint

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

pp = pprint.PrettyPrinter(indent=2)


class FuzzerInputGeneratorAnalyzer(AbstractAnalyzer):
    """
    Generate test cases for the Cairo fuzzer
    """

    NAME = "Fuzzer tests cases generator"
    ARGUMENT = "fuzzer"
    HELP = "Automatically generate fuzzer test cases for each function of the contract"
    IMPACT: ImpactClassification = ImpactClassification.INFORMATIONAL
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    CATEGORY: CategoryClassification = CategoryClassification.ANALYTICS

    def _detect(self) -> bool:
        if self.disassembler.cairo1:
            return False

        path_color = colors.HEADER if self.color else ""
        variable_color = colors.CYAN if self.color else ""

        contract_functions = self.disassembler.functions
        decompiler = Decompiler(functions=contract_functions)
        decompiler.decompile_code(first_pass_only=True)

        symbex = SymbolicExecution(
            variables=decompiler.ssa.memory, assertions=decompiler.assertions
        )

        for function in contract_functions:
            cairo_fuzzer_input = {
                "workspace": "fuzzer_workspace",
                "path": "input_file",
                "name": "Fuzz_one",
                "args": ["felt"] * len(function.args) if function.args is not None else [],
                "inputs": [],
            }

            if function.is_import:
                continue

            test_cases = symbex._generate_test_cases(function=function)
            if not test_cases:
                continue
            self.detected = True

            function_test_cases = "%s\n" % function.name

            paths_count = 0
            for test_case in test_cases:
                test_case_dict = {"value": {"val": [int(str(arg[1])) for arg in test_case]}}
                cairo_fuzzer_input["inputs"].append(test_case_dict)

            function_test_cases += json.dumps(cairo_fuzzer_input, indent=4)
            self.result.append(function_test_cases)

        return self.detected
