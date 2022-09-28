import argparse


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

    # Use a JSON File
    contract_subparser = parser.add_subparsers(help="Load cairo", dest="contract")
    file = contract_subparser.add_parser("file")
    file.add_argument(
        "-path",
        "-path",
        "--path",
        metavar="file",
        type=argparse.FileType("r"),
        required=True,
        help="Cairo compiler JSON",
    )

    # Download a contract from StarkNet mainnet/goerli
    contract = contract_subparser.add_parser("starknet")
    contract.add_argument(
        "-a",
        "-address",
        "--address",
        metavar="address",
        required=True,
        help="address of the contract e.g 0x111111111111111111111111111111111111111111111111111111111111111",
    )
    contract.add_argument(
        "-n",
        "-network",
        "--network",
        metavar="network",
        choices=["mainnet", "goerli"],
        required=True,
        help="Network of the contract, mainnet or goerli",
    )

    m = parser.add_argument_group("optional arguments")
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
        help="Print disassembler/decompiler with color",
    )
    m.add_argument(
        "-a",
        "-analytics",
        "--analytics",
        action="store_true",
        help="Dump a Json file containing debug information",
    )
    m.add_argument(
        "-d", "-decompile", "--decompile", action="store_true", help="Print decompiled code"
    )

    return parser.parse_args()
