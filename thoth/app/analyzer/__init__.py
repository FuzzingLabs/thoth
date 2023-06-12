from thoth.app.analyzer.erc.erc20_detector import ERC20Analyzer
from thoth.app.analyzer.erc.erc721_detector import ERC721Analyzer

from thoth.app.analyzer.strings.strings_analyzer import StringsAnalyzer

from thoth.app.analyzer.testing.tests_cases_generator import TestCasesGeneratorAnalyzer
from thoth.app.analyzer.testing.fuzzer_input_generator import FuzzerInputGeneratorAnalyzer

from thoth.app.analyzer.functions.functions_analyzer import FunctionsAnalyzer

from thoth.app.analyzer.statistics.statistics_analyzer import StatisticsAnalyzer

from thoth.app.analyzer.variables.assignations_analyzer import AssignationsAnalyzer

from thoth.app.analyzer.overflow.integer_overflow_detector import IntegerOverflowDetector

from thoth.app.analyzer.naming.functions_naming_analyzer import FunctionNamingAnalyzer
from thoth.app.analyzer.naming.variables_naming_analyzer import VariableNamingAnalyzer


all_analyzers = [
    # Informational
    ERC20Analyzer,
    ERC721Analyzer,
    StringsAnalyzer,
    TestCasesGeneratorAnalyzer,
    FuzzerInputGeneratorAnalyzer,
    FunctionsAnalyzer,
    StatisticsAnalyzer,
    # Optimization
    AssignationsAnalyzer,
    # Security
    IntegerOverflowDetector,
    FunctionNamingAnalyzer,
    VariableNamingAnalyzer,
]
