import os
import sys
import tempfile
from thoth.app.utils import str_to_bool
from thoth.app.arguments import parse_args
from thoth.app.detectors import all_detectors
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

    # print assembly code
    if args.decompile:
        disassembler.decompiler()
    elif args.disassembly:
        disassembler.print_disassembly()

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

    # Run detectors
    if args.detectors:
        for detector in all_detectors:
            d = detector(disassembler)
            d._detect()
            d._print()
    return 0
