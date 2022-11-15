import argparse
from .. import __version__
from thoth.app.analyzer import all_analyzers
from thoth.app.analyzer.abstract_analyzer import category_classification_text


def parse_args() -> argparse.Namespace:
    """Parse the program arguments

    Returns:
        argparse.Namespace: namespace containing arguments
    """
    root_parser = argparse.ArgumentParser(add_help=False)

    thoth_examples = """
Examples:

Disassemble the contract's compilation artifact from a JSON file:    
    thoth local tests/json_files/cairo_array_sum.json -b

Disassemble the contract's compilation artifact from Starknet:
    thoth remote --address 0x0323D18E2401DDe9aFFE1908e9863cbfE523791690F32a2ff6aa66959841D31D --network mainnet -b

Get a pretty colored version:
    thoth local tests/json_files/cairo_array_sum.json -b -color

Get a verbose version with more details about decoded bytecodes:
    thoth local tests/json_files/cairo_array_sum.json -vvv

Decompile the contract's compilation artifact (json):
    thoth local tests/json_files/cairo_test_addition_if.json -d

Run all the analyzers:
    thoth local tests/json_files/cairo_array_sum.json -a

Select which analyzers to run:
    thoth local tests/json_files/cairo_array_sum.json -a erc20 erc721

Only run a specific category of analyzers:
    thoth local tests/json_files/cairo_array_sum.json -a security
    thoth local tests/json_files/cairo_array_sum.json -a optimization
    thoth local tests/json_files/cairo_array_sum.json -a analytics

Print a list of all the availables analyzers:
    thoth local tests/json_files/cairo_array_sum.json --analyzers-help

Print the contract's call graph:
    thoth local tests/json_files/cairo_array_sum.json -call -view True

For a specific output format (pdf/svg/png):
    thoth local tests/json_files/cairo_array_sum.json -call -view True -format png

Print the contract's control-flow graph (CFG):
    thoth local tests/json_files/cairo_double_function_and_if.json -cfg -view True

For a specific function:
    thoth local tests/json_files/cairo_double_function_and_if.json -cfg -view True -function "__main__.main"

For a specific output format (pdf/svg/png):
    thoth local tests/json_files/cairo_double_function_and_if.json -cfg -view True -format png"""

    parser = argparse.ArgumentParser(
        add_help=True,
        description='Thoth (pronounced "toss") is a Cairo/Starknet analyzer, disassembler & decompiler written in Python 3. Thoth\'s features also include the generation of the call graph and control-flow graph (CFG) of a given Cairo/Starknet compilation artifact.\n\n'
        + thoth_examples,
        epilog="The exit status is 0 for non-failures and -1 for failures.",
        formatter_class=argparse.RawTextHelpFormatter,
        parents=[root_parser],
    )

    root_parser.add_argument("-v", "--version", action="version", version=f"%(prog)s {__version__}")
    root_parser.add_argument(
        "-vvv",
        "-verbose",
        "--verbose",
        action="store_true",
        help="Print JSON with details of all instructions",
    )

    cfg = root_parser.add_argument_group("CFG, call flow graph and data-flow graph")
    cfg.add_argument(
        "-call",
        "--call",
        action="store_true",
        help="Print call flow graph",
    )
    cfg.add_argument(
        "-cfg",
        "--cfg",
        action="store_true",
        help="Print control flow graph",
    )
    cfg.add_argument(
        "-dfg",
        "--dfg",
        action="store_true",
        help="Print data-flow graph",
    )
    cfg.add_argument(
        "-taint",
        "--taint",
        action="store_true",
        help="Taint function arguments in the DFG",
    )
    cfg.add_argument(
        "-view",
        choices=("True", "False"),
        default=argparse.SUPPRESS,
        help="Set if Thoth should open the output graph or not",
    )
    cfg.add_argument(
        "-output_cfg_folder",
        type=str,
        default="output-cfg",
        help="Set the output folder of the cfg",
    )
    cfg.add_argument(
        "-output_callgraph_folder",
        type=str,
        default="output-callgraph",
        help="Set the output folder of the callflowgraph",
    )
    cfg.add_argument(
        "-output_dfg_folder",
        type=str,
        default="output-dfg",
        help="Set the output folder of the data-flow graph",
    )
    cfg.add_argument(
        "-format",
        "--format",
        metavar="Format of the output file [png-svg-pdf]",
        nargs="?",
        choices=["pdf", "png", "svg"],
        help="Format of the graphs",
    )

    disassembler = root_parser.add_argument_group("Disassembler")
    disassembler.add_argument(
        "-function",
        "--function",
        type=str,
        required=False,
        help="Analyse a specific function",
    )
    disassembler.add_argument(
        "-b",
        "-disas",
        "--disassembly",
        action="store_true",
        help="Disassemble bytecode",
    )
    disassembler.add_argument(
        "-d",
        "-decomp",
        "--decompile",
        action="store_true",
        help="Print decompiled code",
    )
    disassembler.add_argument(
        "-color",
        "--color",
        action="store_true",
        help="Print disassembler/decompiler with color",
    )
    disassembler.add_argument(
        "-o",
        "--output",
        action="store",
        type=argparse.FileType("w"),
        help="Output the result of the disassembler/decompiler to a file",
    )

    # Analyser
    analyzers_names = [analyzer.ARGUMENT for analyzer in all_analyzers]
    analyzers_categories_names = list(
        [category.lower() for category in category_classification_text.values()]
    )
    analyzer = root_parser.add_argument_group("Analyzer")

    analyzer.add_argument(
        "-a",
        "-analyze",
        "--analyzers",
        choices=analyzers_names + analyzers_categories_names,
        help="Run analyzers",
        nargs="*",
    )
    analyzer.add_argument(
        "--analyzers-help", choices=analyzers_names, help="Show analyzers help", nargs="*"
    )

    contract_subparser = parser.add_subparsers(
        help="Load a cairo contract compilation artifact from a file or from starknet",
        dest="contract",
        required=True,
    )
    # Use a JSON file
    file = contract_subparser.add_parser("local", parents=[root_parser])
    file.add_argument("path", type=argparse.FileType("r"), help="Cairo compiled JSON file")

    # Download a contract from StarkNet mainnet/goerli
    contract = contract_subparser.add_parser("remote", parents=[root_parser])
    contract.add_argument(
        "-address",
        "--address",
        required=True,
        help="address of the contract e.g 0x111111111111111111111111111111111111111111111111111111111111111",
    )
    contract.add_argument(
        "-n",
        "-network",
        "--network",
        choices=["mainnet", "goerli"],
        required=True,
        help="Network of the contract, mainnet or goerli",
    )

    return parser.parse_args()
