from sierra.analyzer.functions.functions_analyzer import FunctionsAnalyzer
from sierra.analyzer.security.delegate_call_analyzer import DelegateCallAnalyzer
from sierra.analyzer.statistics.statistics_analyzer import StatisticsAnalyzer

all_analyzers = [
    # Security
    DelegateCallAnalyzer,
    # Informational
    FunctionsAnalyzer,
    StatisticsAnalyzer,
]
