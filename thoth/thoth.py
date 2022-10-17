import os
import sys
import tempfile
from thoth.app.utils import str_to_bool
from thoth.app.arguments import parse_args
from thoth.app.analyzer import all_analyzers
from thoth.app.disassembler.disassembler import Disassembler
from thoth.app.starknet.starknet import StarkNet


def main() -> int:
    """Main function of Thoth

    Returns:
        Int: Return 0
    """
    args = parse_args()
    if (args.call or args.cfg) and ("view" not in args):
        print("Need to set -view option")
        sys.exit()

    # Show analyzers help
    if args.analyzers_help is not None:
        if args.analyzers_help:
            for analyzer_name in args.analyzers_help:
                analyzer = [
                    analyzer for analyzer in all_analyzers if analyzer.ARGUMENT == analyzer_name
                ][0]
                analyzer._print_help()
            return 0
        else:
            for analyzer in all_analyzers:
                analyzer._print_help()
            return 0

    # Load compiled contract from a file
    if args.contract == "local":
        file = args.path
        filename = os.path.basename(args.path.name).split(".")[0]
    # Load compiled contract from starknet API
    else:
        try:
            contract = StarkNet(args.network).get_full_contract(args.address)
        except Exception as e:
            print(e)
            exit()
        file = tempfile.NamedTemporaryFile()
        with open(file.name, "w") as f:
            f.write(contract)
        filename = args.address

    disassembler = Disassembler(file, color=args.color)

    if args.verbose:
        disassembler.dump_json()

    # Decompiler
    if args.decompile:
        output = disassembler.decompiler()
    # Disassembler
    elif args.disassembly:
        output = disassembler.print_disassembly()
    # Save output to file
    if args.output and (args.decompile or args.disassembly):
        with args.output as output_file:
            output_file.write(output)

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

    # Run analyzers
    if args.analyzers is not None:
        if args.analyzers:
            for analyzer_name in args.analyzers:
                analyzer = [
                    analyzer for analyzer in all_analyzers if analyzer.ARGUMENT == analyzer_name
                ][0]
                a = analyzer(disassembler)
                a._detect()
                a._print()
        else:
            for analyzer in all_analyzers:
                a = analyzer(disassembler)
                a._detect()
                a._print()
    return 0
