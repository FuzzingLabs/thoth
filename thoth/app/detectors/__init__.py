from thoth.app.detectors.erc.erc20_detector import DetectERC20
from thoth.app.detectors.erc.erc721_detector import DetectERC721

from thoth.app.detectors.strings.strings_detector import DetectString

from thoth.app.detectors.naming.functions_naming_detector import DetectFunctionNaming
from thoth.app.detectors.naming.variables_naming_detector import DetectVariableNaming

from thoth.app.detectors.overflow.integer_overflow_detector import DetectIntegerOverflow

from thoth.app.detectors.functions.functions_detector import FunctionsDetector

all_detectors = [
    DetectERC20,
    DetectERC721,
    DetectString,
    DetectFunctionNaming,
    DetectVariableNaming,
    DetectIntegerOverflow,
    FunctionsDetector,
]
