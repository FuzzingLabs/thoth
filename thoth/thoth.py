import os
import sys
import tempfile
from thoth.app.utils import str_to_bool
from thoth.app.arguments import parse_args
from thoth.app.analyzer import all_analyzers
from thoth.app.analyzer.abstract_analyzer import (
    CategoryClassification,
    category_classification_text,
)
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
        file = args.path.name
        filename = os.path.basename(args.path.name).split(".")[0]
    # Load compiled contract from starknet API
    else:
        try:
            contract = StarkNet(args.network).get_full_contract(args.address)
        except Exception as e:
            print(e)
            exit()
        file = tempfile.NamedTemporaryFile().name
        with open(file, "w") as f:
            f.write(contract)
        filename = args.address

    disassembler = Disassembler(file, color=args.color)

    if args.verbose:
        disassembler.dump_json()

    # Decompiler
    if args.decompile:
        print(disassembler.decompiler())
        if args.output:
            output = Disassembler(file, color=False).decompiler()
            with args.output as output_file:
                output_file.write(output)
    # Disassembler
    elif args.disassembly:
        print(disassembler.print_disassembly())
        if args.output:
            output = Disassembler(file, color=False).print_disassembly()
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
        if args.color:
            disassembler = Disassembler(file, color=False)
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

    # Find elected analyzers
    selected_analyzers = []
    if args.analyzers is not None:
        if args.analyzers:
            selected_analyzers = []
            for analyzer_name in args.analyzers:
                selected_analyzers.append(
                    [analyzer for analyzer in all_analyzers if analyzer.ARGUMENT == analyzer_name][
                        0
                    ]
                )
        else:
            selected_analyzers = all_analyzers

    # Filter analyzers by category
    if args.category is not None:
        filtered_categories = [
            k for k, v in category_classification_text.items() if v.lower() in args.category
        ]
        selected_analyzers = [a for a in selected_analyzers if a.CATEGORY in filtered_categories]

    # Run analyzers
    for analyzer in selected_analyzers:
        a = analyzer(disassembler)
        a._detect()
        a._print()
    return 0
