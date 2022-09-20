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

    c = parser.add_argument_group("mandatory arguments")
    c.add_argument(
        "-f",
        "-file",
        "--file",
        metavar="file",
        type=argparse.FileType("r"),
        nargs="+",
        required=True,
        help="Cairo compiler JSON",
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
        help="Print disassembler with color",
    )
    m.add_argument(
        "-function",
        "--function",
        type=str,
        required=False,
        help="Print disassembler with color",
    )
    m.add_argument(
        "-a",
        "-analytics",
        "--analytics",
        action="store_true",
        help="Dump a Json file containing debug information",
    )
    m.add_argument("-d", "-decomp", "--decomp", action="store_true")

    return parser.parse_args()
