from thoth.app.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)


class ERC20Analyzer(AbstractAnalyzer):
    """
    Detect if a contract is an ERC20 Token and analyze its properties where applicable
    """

    NAME = "ERC20"
    ARGUMENT = "erc20"
    HELP = "Detect if a contract is an ERC20 Token"
    IMPACT: ImpactClassification = ImpactClassification.NONE
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    CATEGORY: CategoryClassification = CategoryClassification.INFORMATIONAL

    def _detect(self) -> None:
        # Cairo naming convention is snake case
        # https://docs.openzeppelin.com/contracts/2.x/api/token/erc20
        mandatory_erc20_functions_names = set(
            ["total_supply", "balance_of", "transfer", "transfer_from", "approve", "allowance"]
        )

        # Burnable ERC20 mandatory functions
        mandatory_burnable_functions_names = set(["burn", "burnfrom"])

        # Pausable ERC20 mandatory functions
        mandatory_pausable_functions_names = set(["pause", "unpause", "paused"])

        # Mintable ERC20 mandatory functions
        mandatory_mintable_functions_names = set(["mint"])

        # Upgradeable ERC20 mandatory functions
        mandatory_upgradeable_functions_names = set(["upgrade"])

        contract_functions = self.disassembler.functions

        functions_names = set([])
        for function in contract_functions:
            functions_names.add(function.name.split(".")[-1].lower())

        self.detected = mandatory_erc20_functions_names.issubset(functions_names)

        if self.detected:
            burnable = mandatory_burnable_functions_names.issubset(functions_names)
            mintable = mandatory_mintable_functions_names.issubset(functions_names)
            pausable = mandatory_pausable_functions_names.issubset(functions_names)
            upgradeable = mandatory_upgradeable_functions_names.issubset(functions_names)
            if burnable:
                self.result.append("Burnable token")
            if mintable:
                self.result.append("Mintable token")
            if pausable:
                self.result.append("Pausable token")
            if upgradeable:
                self.result.append("Upgradeable token")
