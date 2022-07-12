#!/usr/bin/env python3

import argparse
from disassembler import Disassembler

__title__ = 'CairoDisass'
__version__ = '1.0.0'
#__license__ = 'MPL 2.0'
__description__ = 'Cairo disassembler'
__keywords__ = 'Cairo disassembler'
__author__ = 'FuzzingLabs'
__author_email__ = 'contact@fuzzinglabs.com'
__maintainer__ = 'FuzzingLabs Team'
__maintainer_email__ = 'contact@fuzzinglabs.com'
__url__ = 'https://github.com/FuzzingLabs/cairo_disassembler'
__project_urls__ = {
    'Bug Tracker': 'https://github.com/FuzzingLabs/cairo_disassembler/issues'
}
__download_url__ = "https://github.com/FuzzingLabs/cairo_disassembler/tarball/" + __version__

def parse_args():
    """
    Argument parser for command line
    """
    parser = argparse.ArgumentParser(
        add_help=False,
        description='Cairo Disassembler',
        epilog='The exit status is 0 for non-failures and -1 for failures.',
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
        prog=__title__
    )

    c = parser.add_argument_group('mandatory arguments')
    c.add_argument('-f', '-file', '--file', metavar='file', type=argparse.FileType('r'), nargs='+', required=True, help='Cairo compiler JSON')
    
    m = parser.add_argument_group('optional arguments')
    m.add_argument('-vvv', '-verbose', '--verbose', action='store_true', help='Print JSON with details of all instructions')
    m.add_argument('-c', '-call', '--call', action='store_true', help='Print call flow graph')

    return parser.parse_args()



def main():
    """
    Main function
    """
    args = parse_args()
    disassembler = Disassembler(args.file)

    if ("vvv" in vars(args) and args.vvv):
        disassembler.dump_json()
    if ("call" in vars(args) and args.call):
        disassembler.print_call_flow_graph()
    disassembler.print()
    return 0

if __name__ == "__main__":
    main()