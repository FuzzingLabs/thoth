import argparse


def parse_arguments() -> argparse.Namespace:
    # Create the parser
    parser = argparse.ArgumentParser(
        description="""
    thoth-sierra is a tool that can analyze Sierra files and generate their Control-Flow and Call-Flow graphs.
    """
    )

    # Add arguments
    parser.add_argument("-f", "--file", required=True, help="Path of the sierra file")
    parser.add_argument("--call", help="Generate a call-flow graph", action="store_true")
    parser.add_argument("--cfg", help="Generate a control-flow graph", action="store_true")

    # Parse the arguments
    args = parser.parse_args()

    return args
