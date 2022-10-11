from thoth.app.utils import field_element_repr
from thoth.app.detectors.abstract_detector import AbstractDetector, DetectorClassification


class DetectString(AbstractDetector):
    """
    Detect strings inside a contract
    """

    NAME = "Strings"
    ARGUMENT = "strings"
    HELP = "Detect strings inside a contract"
    IMPACT = DetectorClassification.INFORMATIONAL

    def _detect(self) -> None:
        contract_functions = self.disassembler.functions

        for function in contract_functions:
            for instruction in function.instructions:
                if "OP1" in instruction.res and "IMM" in instruction.op1Addr:
                    representation = field_element_repr(int(instruction.imm), instruction.prime)
                    # Check if this is a string
                    if representation[:2] != "0x":
                        try:
                            representation_hex = hex(int(representation))
                            representation_str = bytearray.fromhex(representation_hex[2:]).decode(
                                "utf-8"
                            )
                            if representation_str.isprintable():
                                self.detected = True
                                self.result.append(representation_str)
                        except:
                            pass
