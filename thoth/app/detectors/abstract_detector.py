from enum import Enum
from typing import List
from thoth.app.disassembler.disassembler import Disassembler


class DetectorClassification(Enum):
    HIGH = 0
    MEDIUM = 1
    LOW = 2
    INFORMATIONAL = 3
    OPTIMIZATION = 4

    UNIMPLEMENTED = 999


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

    def __init__(self, disassembler: Disassembler) -> None:
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

        title = "[%s]" % self.NAME
        print(title)
        for result in self.result:
            print("%s" % result)
        return True
