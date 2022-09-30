import os
import sys
from thoth.app.utils import str_to_bool
from thoth.app.arguments import parse_args
from thoth.app.disassembler.disassembler import Disassembler


def main() -> int:
    """Main function of Thoth

    Returns:
        Int: Return 0
    """
    args = parse_args()
    if (args.call or args.cfg) and ("view" not in args):
        print("help")
        sys.exit()
    disassembler = Disassembler(args.file, color=args.color)

    if args.verbose:
        disassembler.dump_json()

    # print assembly code
    if args.decompile:
        disassembler.decompiler()
    else:
        disassembler.print_disassembly()

    filename = os.path.basename(args.file[0].name).split(".")[0]
    format = "pdf" if args.format is None else str(args.format)

    # print call flow graph
    if args.call:
        disassembler.print_call_flow_graph(
            folder=args.output_callgraph_folder,
            filename=filename,
            format=format,
            view=str_to_bool(args.view),
        )

    # print CFG
    if args.cfg:
        disassembler.print_cfg(
            folder=args.output_cfg_folder,
            filename=filename,
            format=format,
            function_name=args.function,
            view=str_to_bool(args.view),
        )

    # print analytics
    if args.analytics:
        print(disassembler.analytics())
    return 0
