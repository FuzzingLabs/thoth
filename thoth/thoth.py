#!/usr/bin/env python3

import argparse
import os
from thoth import utils
from .disassembler import Disassembler


def parse_args():
    """Parse the program arguments

    Returns:
        list: list containing arguments 
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
    m.add_argument("-c", "-call", "--call", action="store_true", help="Print call flow graph")
    m.add_argument("-g", "-cfg", "--cfg", action="store_true", help="Print control flow graph")
    m.add_argument(
        "-format",
        "--format",
        metavar="Format of the output file [png-svg-pdf]",
        nargs="?",
        choices=["pdf", "png", "svg"],
        help="Format of the graphs",
    )
    m.add_argument("-color", "--color", action="store_true", help="Print disassembler with color")
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

    return parser.parse_args()


def main():
    """
    Main function
    """
    args = parse_args()
    disassembler = Disassembler(args.file, color=args.color)

    if args.verbose:
        disassembler.dump_json()

    # print assembly code
    disassembler.print_disassembly()
    filename = os.path.basename(args.file[0].name).split(".")[0]
    format = "pdf" if args.format is None else str(args.format)
    # print call flow graph
    if args.call:
        disassembler.print_call_flow_graph(filename=filename, format=format)

    # print CFG
    if args.cfg:
        disassembler.print_cfg(filename=filename, format=format, func_name=args.function)

    # print analytics
    if args.analytics:
        print(disassembler.analytics())

    return 0


if __name__ == "__main__":
    main()
