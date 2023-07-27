from sierra.analyzer.functions.functions_analyzer import FunctionsAnalyzer
from sierra.analyzer.security.dead_code_analyzer import DeadCodeAnalyzer
from sierra.analyzer.security.delegate_call_analyzer import DelegateCallAnalyzer
from sierra.analyzer.security.user_defined_function_call_analyzer import (
    UserDefinedFunctionCallAnalyzer,
)
from sierra.analyzer.security.usused_arguments_analyzer import UnusedArgumentsAnalyzer
from sierra.analyzer.statistics.statistics_analyzer import StatisticsAnalyzer
from sierra.analyzer.strings.strings_analyzer import StringsAnalyzer


all_analyzers = [
    # Security
    UserDefinedFunctionCallAnalyzer,
    DeadCodeAnalyzer,
    DelegateCallAnalyzer,
    UnusedArgumentsAnalyzer,
    # Informational
    FunctionsAnalyzer,
    StatisticsAnalyzer,
    StringsAnalyzer,
]
