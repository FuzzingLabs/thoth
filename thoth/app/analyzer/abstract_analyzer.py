from enum import Enum
from sre_parse import CATEGORIES
from typing import Callable, Dict, List
from unicodedata import category
from thoth.app.disassembler.disassembler import Disassembler


class colors:
    HEADER = "\033[95m"
    CYAN = "\033[96m"
    GREEN = "\033[92m"
    YELLOW = "\033[93m"
    RED = "\033[91m"
    ENDC = "\033[0m"


class PrecisionClassification(Enum):
    """
    Level of precision of an analyzer
    """

    LOW = 0
    MEDIUM = 1
    HIGH = 2


class ImpactClassification(Enum):
    """
    Level of impact of a security detector
    Analytics/Optimization analyzers have a NONE Impact by default
    """

    INFORMATIONAL = 0
    HIGH = 1
    MEDIUM = 2
    LOW = 3


class CategoryClassification(Enum):
    """
    Analyzer category
    """

    ANALYTICS = 0
    OPTIMIZATION = 1
    SECURITY = 2

    UNIMPLEMENTED = 999


category_classification_colors: Dict[CategoryClassification, str] = {
    CategoryClassification.ANALYTICS: colors.GREEN,
    CategoryClassification.OPTIMIZATION: colors.CYAN,
    CategoryClassification.SECURITY: colors.RED,
}

category_classification_text: Dict[CategoryClassification, str] = {
    CategoryClassification.ANALYTICS: "Analytics",
    CategoryClassification.OPTIMIZATION: "Optimization",
    CategoryClassification.SECURITY: "Security",
}

impact_classification_colors: Dict[ImpactClassification, str] = {
    ImpactClassification.INFORMATIONAL: colors.CYAN,
    ImpactClassification.LOW: colors.GREEN,
    ImpactClassification.MEDIUM: colors.YELLOW,
    ImpactClassification.HIGH: colors.RED,
}

impact_classification_text: Dict[ImpactClassification, str] = {
    ImpactClassification.INFORMATIONAL: "Informational",
    ImpactClassification.LOW: "Low",
    ImpactClassification.MEDIUM: "Medium",
    ImpactClassification.HIGH: "High",
}


class AbstractAnalyzer:
    """
    Base class from which all analyzers inherit
    """

    # Analyzer name
    NAME = ""
    # Name to use in CLI to select the analyzer
    ARGUMENT = ""
    # Analyzer description
    HELP = ""
    # Analyzer impact
    IMPACT: ImpactClassification = ImpactClassification.INFORMATIONAL
    # Analyzer precision
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    # Analyzer category
    CATEGORY: CategoryClassification = CategoryClassification.UNIMPLEMENTED

    def __init__(self, disassembler: Disassembler, color: bool = True) -> None:
        """
        Detector initialization
        """
        self.disassembler = disassembler
        self.result: List[str] = []
        self.detected = False
        self.color = color

    def _detect(self) -> bool:
        """
        Run analyzer on the contract
        """
        pass

    @classmethod
    def _print_help(cls, color: bool = True) -> None:
        """
        Print the analyzer documentation
        """
        category_color = category_classification_colors[cls.CATEGORY] if color else ""
        help = "[%s] %s%s%s <%s> - " % (
            category_classification_text[cls.CATEGORY],
            category_color,
            cls.NAME,
            colors.ENDC,
            cls.ARGUMENT,
        )
        help += "%s" % cls.HELP
        print(help)

    def _print(self) -> bool:
        """
        Print the detector result
        """
        if not self.detected:
            return False

        # Impact
        impact = ""
        if self.CATEGORY == CategoryClassification.SECURITY:
            impact_color = impact_classification_colors[self.IMPACT] if self.color else ""
            impact = "(%s)" % (impact_color + impact_classification_text[self.IMPACT] + colors.ENDC)

        category_color = category_classification_colors[self.CATEGORY] if self.color else ""
        title = "[%s%s%s] %s %s" % (
            category_color,
            category_classification_text[self.CATEGORY],
            colors.ENDC,
            self.NAME,
            impact,
        )
        print(title)
        for result in self.result:
            print("  -  %s" % result)
        return True
