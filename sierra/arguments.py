import argparse
import os.path

from sierra.analyzer import all_analyzers
from sierra.analyzer.abstract_analyzer import category_classification_text


def is_valid_file(parser: argparse.ArgumentParser, path: str) -> str:
    """
    Check if the sierra file path is valid
    """
    if not os.path.exists(path):
        parser.error("The file %s does not exist" % path)
    return path


def parse_arguments() -> argparse.Namespace:
    """
    Parse the thoth-sierra arguments
    """
    # Create the parser
    parser = argparse.ArgumentParser(
        description="""
    thoth-sierra is a tool that can analyze Sierra files and generate their Control-Flow and Call-Graphs.
    """
    )

    # Global arguments
    parser.add_argument(
        "-f",
        "--file",
        help="Path of the sierra file",
        type=lambda path: is_valid_file(parser, path),
    )
    parser.add_argument("--decompile", "-d", help="Decompile the sierra file", action="store_true")
    parser.add_argument(
        "--format",
        help="Decompile the sierra file",
        nargs="?",
        choices=["pdf", "png", "svg"],
        default="pdf",
    )

    # CFG
    cfg = parser.add_argument_group("Call-Flow Graph")
    cfg.add_argument("--cfg", help="Generate a control-flow graph", action="store_true")
    cfg.add_argument(
        "-output_cfg_folder",
        type=str,
        default="output-cfg",
        help="Set the output folder of the CFG (default is ./output-cfg)",
    )

    # Callgraph
    callgraph = parser.add_argument_group("Call-Graph")
    callgraph.add_argument("--call", help="Generate a call-graph", action="store_true")
    callgraph.add_argument(
        "-output_callgraph_folder",
        type=str,
        default="output-callgraph",
        help="Set the output folder of the Call-Graph (default is ./output-callgraph)",
    )

    # Analyzers
    analyzers_names = [analyzer.ARGUMENT for analyzer in all_analyzers]
    analyzers_categories_names = list(
        [category.lower() for category in category_classification_text.values()]
    )

    parser.add_argument(
        "-a",
        "-analyze",
        "--analyzers",
        choices=analyzers_names + analyzers_categories_names,
        help="Run analyzers",
        nargs="*",
    )
    parser.add_argument(
        "--analyzers-help", choices=analyzers_names, help="Show analyzers help", nargs="*"
    )

    # Parse the arguments
    args = parser.parse_args()

    return args
