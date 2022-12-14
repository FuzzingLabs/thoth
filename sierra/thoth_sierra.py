from sierra import config
from sierra.callgraph.callgraph import SierraCallGraph
from sierra.arguments import parse_arguments
from sierra.parser.parser import SierraParser


def main() -> None:

    args = parse_arguments()

    sierra_file = args.file
    try:
        parser = SierraParser(config.SIERRA_LARK_PARSER_PATH)
        parser.parse(sierra_file)
    except Exception as e:
        print("%s is not a valid sierra file" % "a")
        return

    if args.cfg:
        parser.print_cfg()

    if args.call:
        callgraph = SierraCallGraph(parser)
        callgraph._generate_callgraph()

        callgraph._print_callgraph()
