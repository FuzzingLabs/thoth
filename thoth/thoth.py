import os
from thoth.app.arguments import parse_args
from thoth.app.disassembler.disassembler import Disassembler


def main() -> int:
    """Main function of Thoth

    Returns:
        Int: Return 0
    """
    args = parse_args()
    disassembler = Disassembler(args.file, color=args.color)

    if args.verbose:
        disassembler.dump_json()

    # print assembly code
    if args.decomp:
        disassembler.decompiler()
    else:
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
