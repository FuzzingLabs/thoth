from sierra.analyzer.functions.functions_analyzer import FunctionsAnalyzer
from sierra.analyzer.security.dead_code_analyzer import DeadCodeAnalyzer
from sierra.analyzer.security.delegate_call_analyzer import DelegateCallAnalyzer
from sierra.analyzer.security.integer_overflow_analyzer import IntegerOverflowAnalyzer
from sierra.analyzer.security.user_defined_function_call_analyzer import (
    UserDefinedFunctionCallAnalyzer,
)
from sierra.analyzer.security.usused_arguments_analyzer import UnusedArgumentsAnalyzer
from sierra.analyzer.statistics.statistics_analyzer import StatisticsAnalyzer
from sierra.analyzer.strings.strings_analyzer import StringsAnalyzer


all_analyzers = [
    # Secturity
    DelegateCallAnalyzer,
    IntegerOverflowAnalyzer,

    # Optimization
    DeadCodeAnalyzer,
    UnusedArgumentsAnalyzer,
    UserDefinedFunctionCallAnalyzer,
    
    # Informational
    FunctionsAnalyzer,
    StatisticsAnalyzer,
    StringsAnalyzer,
]
