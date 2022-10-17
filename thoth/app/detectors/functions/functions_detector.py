from thoth.app.utils import field_element_repr
from thoth.app.detectors.abstract_detector import AbstractDetector, DetectorClassification


class FunctionsDetector(AbstractDetector):
    """
    Detect strings inside a contract
    """

    NAME = "Functions"
    ARGUMENT = "functions"
    HELP = "Retrieve informations about the contract's functions"
    IMPACT = DetectorClassification.INFORMATIONAL

    def _detect(self) -> None:
        contract_functions = [
            function for function in self.disassembler.functions if not function.is_import
        ]
        self.detected = bool(contract_functions)

        for function in contract_functions:
            result = "%s" % function.name
            decorators = [decorator for decorator in function.decorators]
            if decorators:
                result += "\n"
                result += "\t- decorators : %s" % ", ".join(decorators)
            self.result.append(result)
