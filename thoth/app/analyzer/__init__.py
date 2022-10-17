from thoth.app.analyzer.erc.erc20_detector import ERC20Analyzer
from thoth.app.analyzer.erc.erc721_detector import ERC721Analyzer

from thoth.app.analyzer.strings.strings_analyzer import StringsAnalyzer

from thoth.app.analyzer.naming.functions_naming_analyzer import FunctionNamingAnalyzer
from thoth.app.analyzer.naming.variables_naming_analyzer import VariableNamingAnalyzer

from thoth.app.analyzer.overflow.integer_overflow_detector import IntegerOverflowDetector

from thoth.app.analyzer.functions.functions_analyzer import FunctionsAnalyzer

all_analyzers = [
    ERC20Analyzer,
    ERC721Analyzer,
    StringsAnalyzer,
    FunctionNamingAnalyzer,
    IntegerOverflowDetector,
    FunctionsAnalyzer,
]
