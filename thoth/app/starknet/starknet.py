import requests

GOERLI_NETWORK_ADRESS = "https://alpha4.starknet.io"
MAINNET_NETWORK_ADRESS = "https://alpha-mainnet.starknet.io"


class StarkNet:
    """
    Interact with StarkNet
    """

    def __init__(self, network: str) -> None:
        """
        Initialize the connection with starknet mainnet/goerli
        """
        self.network = network

    def get_full_contract(self, contract_adress: str) -> str:
        """
        Get a JSON contract from starknet
        """
        # Main network
        if self.network == "mainnet":
            api_url = MAINNET_NETWORK_ADRESS
        # Goerli Network
        else:
            api_url = GOERLI_NETWORK_ADRESS

        contract_url = (
            f"{api_url}/feeder_gateway/get_full_contract?contractAddress={contract_adress}"
        )
        full_contract = requests.get(contract_url)

        # If the contract does not exist
        if full_contract.status_code != 200:
            raise ValueError(
                f"Thoth could not find contract at adress {contract_adress} in {self.network} network"
            )
        return full_contract.text
