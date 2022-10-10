from thoth.app.detectors.erc.erc20_detector import DetectERC20
from thoth.app.detectors.erc.erc721_detector import DetectERC721

from thoth.app.detectors.strings.strings_detector import DetectString

all_detectors = [DetectERC20, DetectERC721, DetectString]
