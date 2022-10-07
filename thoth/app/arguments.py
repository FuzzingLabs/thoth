import argparse
from .. import __version__


def parse_args() -> argparse.Namespace:
    """Parse the program arguments

    Returns:
        argparse.Namespace: namespace containing arguments
    """
    parser = argparse.ArgumentParser(
        add_help=True,
        description="Cairo Disassembler",
        epilog="The exit status is 0 for non-failures and -1 for failures.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )

    contract_subparser = parser.add_subparsers(
        help="Load a cairo contract compilation artifact from a file or from starknet",
        dest="contract",
        required=True,
    )
    # Use a JSON file
    file = contract_subparser.add_parser("file")
    file.add_argument(
        "-path",
        "-path",
        "--path",
        type=argparse.FileType("r"),
        required=True,
        help="Cairo compiled JSON file",
    )

    # Download a contract from StarkNet mainnet/goerli
    contract = contract_subparser.add_parser("starknet")
    contract.add_argument(
        "-a",
        "-address",
        "--address",
        required=True,
        help="address of the contract e.g 0x111111111111111111111111111111111111111111111111111111111111111",
    )
    contract.add_argument(
        "-n",
        "-network",
        "--network",
        choices=["mainnet", "goerli"],
        required=True,
        help="Network of the contract, mainnet or goerli",
    )

    m = parser.add_argument_group("optional arguments")
    m.add_argument("-v", "--version", action="version", version=f"%(prog)s {__version__}")
    m.add_argument(
        "-vvv",
        "-verbose",
        "--verbose",
        action="store_true",
        help="Print JSON with details of all instructions",
    )
    m.add_argument(
        "-c",
        "-call",
        "--call",
        action="store_true",
        help="Print call flow graph",
    )
    m.add_argument(
        "-g",
        "-cfg",
        "--cfg",
        action="store_true",
        help="Print control flow graph",
    )
    m.add_argument(
        "-view",
        choices=("True", "False"),
        default=argparse.SUPPRESS,
        help="Set if Thoth should open the output graph or not",
    )
    m.add_argument(
        "-output_cfg_folder",
        type=str,
        default="output-cfg",
        help="Set the output folder of the cfg",
    )
    m.add_argument(
        "-output_callgraph_folder",
        type=str,
        default="output-callgraph",
        help="Set the output folder of the callflowgraph",
    )
    m.add_argument(
        "-format",
        "--format",
        metavar="Format of the output file [png-svg-pdf]",
        nargs="?",
        choices=["pdf", "png", "svg"],
        help="Format of the graphs",
    )
    m.add_argument(
        "-color",
        "--color",
        action="store_true",
        help="Print disassembler/decompiler with color",
    )
    m.add_argument(
        "-function",
        "--function",
        type=str,
        required=False,
        help="Analyse a specific function",
    )
    m.add_argument(
        "-a",
        "-analytics",
        "--analytics",
        action="store_true",
        help="Dump a Json file containing debug information",
    )
    m.add_argument(
        "-d",
        "-decompile",
        "--decompile",
        action="store_true",
        help="Print decompiled code",
    )

    return parser.parse_args()
