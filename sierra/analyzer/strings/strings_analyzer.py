import binascii
import re

from sierra.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)


class StringsAnalyzer(AbstractAnalyzer):
    """
    Extract strings from a contract
    """

    NAME = "Strings"
    ARGUMENT = "strings"
    HELP = "Extract strings"
    IMPACT: ImpactClassification = ImpactClassification.INFORMATIONAL
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    CATEGORY: CategoryClassification = CategoryClassification.ANALYTICS

    def _detect(self) -> bool:
        self.detected = True

        string_regex = r"const<([0-9]+)>"

        libfuncs = self.program.libfuncs
        for libfunc in libfuncs:
            match = re.findall(string_regex, libfunc.name)
            if match:
                try:
                    string = binascii.unhexlify("{:x}".format(int(match[0]))).decode()
                    self.result.append(string)
                except:
                    pass
        return self.detected
