#!/usr/bin/env python3

import argparse
from dis import disassemble
import logging
from classData import Disassembler
import graphviz

from __version__ import __version__, __title__
from disassembler import *
from utils import *
from jsonParser import *

class CairoDisassCommandLine:
    @staticmethod
    def parse_args():
        parser = argparse.ArgumentParser(
            add_help=False,
            description='Cairo Disassembler',
            epilog='The exit status is 0 for non-failures and -1 for failures.',
            formatter_class=argparse.ArgumentDefaultsHelpFormatter,
            prog=__title__
        )

        c = parser.add_argument_group('mandatory arguments')
        c.add_argument('-file', metavar='file', type=argparse.FileType('r'), nargs='+', required=True, help='Cairo File')
        
        m = parser.add_argument_group('optional arguments')
        m.add_argument('-vvv',  action='store_true', help='Print JSON with details of all offset')
        m.add_argument('-call', action='store_true', help='Print call flow graph')

        return parser.parse_args()


    @classmethod
    def main(cls):
        args = cls.parse_args()
        disassembler = Disassembler(args.file)
        if ("vvv" in vars(args) and args.vvv):
            disassembler.dumpJson()
        if ("call" in vars(args) and args.call):
            disassembler.printCallFlowGraph()
        disassembler.printDisass()
        return 0