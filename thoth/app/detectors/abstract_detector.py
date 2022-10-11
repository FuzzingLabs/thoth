from enum import Enum
from typing import Callable, Dict, List
from thoth.app.disassembler.disassembler import Disassembler


class colors:
    GREEN = "\033[92m"
    YELLOW = "\033[93m"
    RED = "\033[91m"
    ENDC = "\033[0m"


class DetectorClassification(Enum):
    HIGH = 0
    MEDIUM = 1
    LOW = 2
    INFORMATIONAL = 3
    OPTIMIZATION = 4

    UNIMPLEMENTED = 999


classification_colors: Dict[DetectorClassification, Callable[[str], str]] = {
    DetectorClassification.INFORMATIONAL: colors.GREEN,
    DetectorClassification.OPTIMIZATION: colors.GREEN,
    DetectorClassification.LOW: colors.GREEN,
    DetectorClassification.MEDIUM: colors.YELLOW,
    DetectorClassification.HIGH: colors.RED,
}

classification_text: Dict[DetectorClassification, str] = {
    DetectorClassification.INFORMATIONAL: "Informational",
    DetectorClassification.OPTIMIZATION: "Optimization",
    DetectorClassification.LOW: "Low",
    DetectorClassification.MEDIUM: "Medium",
    DetectorClassification.HIGH: "High",
}


class AbstractDetector:
    """
    Base class from which all detectors inherit
    """

    # Detector name
    NAME = ""
    # Name to use in CLI to select the detector
    ARGUMENT = ""
    # Detector description
    HELP = ""
    # Detector impact
    IMPACT: DetectorClassification = DetectorClassification.UNIMPLEMENTED

    def __init__(self, disassembler: Disassembler, color: bool = False) -> None:
        """
        Detector initialization
        """
        self.disassembler = disassembler
        self.result: List[str] = []
        self.detected = False

    def _detect(self) -> None:
        """
        Run the detector on the contract
        """
        pass

    def _print(self) -> bool:
        """
        Print the detector result
        """
        if not self.detected:
            return False

        title = "[%s%s%s] %s" % (
            classification_colors[self.IMPACT],
            classification_text[self.IMPACT],
            colors.ENDC,
            self.NAME,
        )
        print(title)
        for result in self.result:
            print("    - %s" % result)
        return True
