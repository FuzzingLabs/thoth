import os
import tempfile
from thoth.app.arguments import parse_args
from thoth.app.disassembler.disassembler import Disassembler
from thoth.app.starknet.starknet import StarkNet


def main() -> int:
    """Main function of Thoth

    Returns:
        Int: Return 0
    """
    args = parse_args()

    # Load compiled contract from a file 
    if args.contract == "file":
        file = args.path
        filename = os.path.basename(args.path.name).split(".")[0]
    # Load compiled contract from starknet API 
    else:
        try:
            contract = StarkNet(args.network).get_full_contract(args.adress)
        except Exception as e:
            print(e)
            exit()
        file = tempfile.NamedTemporaryFile()
        with open(file.name, "w") as f:
            f.write(contract)
        filename = args.adress

    disassembler = Disassembler(file, color=args.color)

    if args.verbose:
        disassembler.dump_json()

    # print assembly code
    if args.decompile:
        disassembler.decompiler()
    else:
        disassembler.print_disassembly()

    format = "pdf" if args.format is None else str(args.format)

    # print call flow graph
    if args.call:
        disassembler.print_call_flow_graph(filename=filename, format=format)

    # print CFG
    if args.cfg:
        disassembler.print_cfg(filename=filename, format=format, function_name=args.function)

    # print analytics
    if args.analytics:
        print(disassembler.analytics())
    return 0
