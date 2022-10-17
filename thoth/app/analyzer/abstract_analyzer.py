from enum import Enum
from sre_constants import CATEGORY
from typing import Callable, Dict, List
from thoth.app.disassembler.disassembler import Disassembler


class colors:
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
    Informational/Optimization analyzers have a NONE Impact by default
    """

    NONE = 0
    HIGH = 1
    MEDIUM = 2
    LOW = 3


class CategoryClassification(Enum):
    """
    Analyzer category
    """

    INFORMATIONAL = 0
    OPTIMIZATION = 1
    SECURITY = 2

    UNIMPLEMENTED = 999


category_classification_colors: Dict[CategoryClassification, Callable[[str], str]] = {
    CategoryClassification.INFORMATIONAL: colors.GREEN,
    CategoryClassification.OPTIMIZATION: colors.CYAN,
    CategoryClassification.SECURITY: colors.RED,
}

category_classification_text: Dict[CategoryClassification, str] = {
    CategoryClassification.INFORMATIONAL: "Informational",
    CategoryClassification.OPTIMIZATION: "Optimization",
    CategoryClassification.SECURITY: "Security",
}

impact_classification_colors: Dict[ImpactClassification, Callable[[str], str]] = {
    ImpactClassification.NONE: colors.CYAN,
    ImpactClassification.LOW: colors.GREEN,
    ImpactClassification.MEDIUM: colors.YELLOW,
    ImpactClassification.HIGH: colors.RED,
}

impact_classification_text: Dict[ImpactClassification, str] = {
    ImpactClassification.NONE: "None",
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
    IMPACT: ImpactClassification = ImpactClassification.NONE
    # Analyzer precision
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    # Analyzer category
    CATEGORY: CategoryClassification = CategoryClassification.UNIMPLEMENTED

    def __init__(self, disassembler: Disassembler) -> None:
        """
        Detector initialization
        """
        self.disassembler = disassembler
        self.result: List[str] = []
        self.detected = False

    def _detect(self) -> None:
        """
        Run analyzerdetector on the contract
        """
        pass

    def _print(self) -> bool:
        """
        Print the detector result
        """
        if not self.detected:
            return False

        title = "[%s%s%s] %s" % (
            category_classification_colors[self.CATEGORY],
            category_classification_text[self.CATEGORY],
            colors.ENDC,
            self.NAME,
        )
        print(title)
        for result in self.result:
            print("  -  %s" % result)
        return True
