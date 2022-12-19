from sierra import config
from sierra.callgraph.callgraph import SierraCallGraph
from sierra.arguments import parse_arguments
from sierra.parser.parser import SierraParser
from sierra.decompiler.decompiler import SierraDecompiler


def main() -> None:

    args = parse_arguments()

    # Parse a Sierra file
    sierra_file = args.file
    try:
        parser = SierraParser(config.SIERRA_LARK_PARSER_PATH)
        parser.parse(sierra_file)
    except Exception:
        print("%s is not a valid sierra file" % sierra_file)
        return

    # Control-Flow Graph
    if args.cfg:
        parser.print_cfg()

    # Call-Graph
    if args.call:
        callgraph = SierraCallGraph(parser)
        callgraph.generate_callgraph()

        callgraph.print_callgraph()

    # Decompiler
    if args.decompile:
        decompiler = SierraDecompiler(program=parser)
        decompiled_code = decompiler.decompile_code()
        print(decompiled_code)
