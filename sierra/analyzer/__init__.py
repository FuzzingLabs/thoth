from sierra.analyzer.functions.functions_analyzer import FunctionsAnalyzer
from sierra.analyzer.security.delegate_call_analyzer import DelegateCallAnalyzer
from sierra.analyzer.security.reentrancy_guards_analyzer import ReentrancyGuardsAnalyzer
from sierra.analyzer.statistics.statistics_analyzer import StatisticsAnalyzer
from sierra.analyzer.strings.strings_analyzer import StringsAnalyzer

all_analyzers = [
    # Security
    DelegateCallAnalyzer,
    ReentrancyGuardsAnalyzer,
    # Informational
    FunctionsAnalyzer,
    StringsAnalyzer,
    StatisticsAnalyzer,
]
