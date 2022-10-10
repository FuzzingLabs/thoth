from thoth.app.detectors.abstract_detector import AbstractDetector, DetectorClassification


class DetectERC721(AbstractDetector):
    """
    Detect if a contract is an ERC20 Token
    """

    NAME = "Detect ERC721"
    ARGUMENT = "detect_erc721"
    HELP = "Detect if a contract is an ERC721 Token"
    IMPACT = DetectorClassification.INFORMATIONAL

    def _detect(self) -> None:
        contract_functions = self.disassembler.functions

        for function in contract_functions:
            if "openzeppelin.token.erc721.library" in function.name:
                self.detected = True
                break
        if self.detected:
            self.result.append("ERC721 Token detected")
