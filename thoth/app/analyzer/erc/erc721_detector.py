from thoth.app.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)


class ERC721Analyzer(AbstractAnalyzer):
    """
    Detect if a contract is an ERC20 Token and analyze its properties where applicable
    """

    NAME = "ERC721"
    ARGUMENT = "erc721"
    HELP = "Detect if a contract is an ERC721 Token"
    IMPACT: ImpactClassification = ImpactClassification.INFORMATIONAL
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    CATEGORY: CategoryClassification = CategoryClassification.ANALYTICS

    def _detect(self) -> bool:
        # Cairo naming convention is snake case
        # https://docs.openzeppelin.com/contracts/2.x/api/token/erc721
        mandatory_erc721_functions_names = set(
            [
                "balance_of",
                "owner_of",
                "safe_transfer_from",
                "transfer_from",
                "approve",
                "get_approved",
                "set_approval_for_all",
                "is_approved_for_all",
                "safe_transfer_from",
            ]
        )

        # Mintable ERC721 mandatory functions
        mandatory_mintable_functions_names = set(["mint"])

        # Burnable ERC721 mandatory functions
        mandatory_burnable_functions_names = set(["burn"])

        # Pausable ERC721 mandatory functions
        mandatory_pausable_functions_names = set(["pause", "unpause", "paused"])

        # Enumerable ERC721 mandatory functions
        mandatory_enumerable_functions_names = set(
            ["totalsupply", "tokenofownerbyindex", "tokenbyindex"]
        )

        contract_functions = self.disassembler.functions

        functions_names = set([])
        for function in contract_functions:
            functions_names.add(function.name.split(".")[-1].lower())

        self.detected = mandatory_erc721_functions_names.issubset(functions_names)
        if self.detected:
            mintable = mandatory_mintable_functions_names.issubset(functions_names)
            burnable = mandatory_burnable_functions_names.issubset(functions_names)
            pausable = mandatory_pausable_functions_names.issubset(functions_names)
            enumerable = mandatory_enumerable_functions_names.issubset(functions_names)
            if mintable:
                self.result.append("Mintable token")
            if burnable:
                self.result.append("Burnable token")
            if pausable:
                self.result.append("Pausable token")
            if enumerable:
                self.result.append("Enumerable token")
        return self.detected
