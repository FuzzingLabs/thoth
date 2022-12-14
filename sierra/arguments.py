import argparse
import os.path


def is_valid_file(parser: argparse.ArgumentParser, path: str) -> str:
    """
    Check if the sierra file path is valid
    """
    if not os.path.exists(path):
        parser.error("The file %s does not exist" % path)
    return path


def parse_arguments() -> argparse.Namespace:
    """
    PArse the thoth-sierra arguments
    """
    # Create the parser
    parser = argparse.ArgumentParser(
        description="""
    thoth-sierra is a tool that can analyze Sierra files and generate their Control-Flow and Call-Graphs.
    """
    )

    # Add arguments
    parser.add_argument(
        "-f",
        "--file",
        required=True,
        help="Path of the sierra file",
        type=lambda path: is_valid_file(parser, path),
    )
    parser.add_argument("--call", help="Generate a call-flow graph", action="store_true")
    parser.add_argument("--cfg", help="Generate a control-flow graph", action="store_true")

    # Parse the arguments
    args = parser.parse_args()

    return args
