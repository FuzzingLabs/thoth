#!/usr/bin/env python3

import argparse
import logging

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

        subparser = parser.add_subparsers(dest='mode', help ='cairo/starknet')

        c = subparser.add_parser('cairo')
        c.add_argument('-file', metavar='file', type=argparse.FileType('r'), nargs='+', required=True,
                       help='Cairo File')

        s = subparser.add_parser('starknet')
        s.add_argument('-file', metavar='file', type=argparse.FileType('r'), nargs='+', required=True,
                       help='CairoFile')
        return parser.parse_args()


    @classmethod
    def main(cls):
        args = cls.parse_args()
        logging.basicConfig(format='[CairoDisass] %(asctime)s %(levelname)s: %(message)s')
        handler = logging.StreamHandler()
        handler.terminator = "\r"
        logging.getLogger().addHandler(handler)
        logging.getLogger().setLevel(logging.INFO)   
        logging.info(f"CairoDisass -- File : {args.file[0].name}")

        disassJson = parseToJson(args.file)
        headFunction = analyzeGetFunctions(disassJson)
        while (headFunction):
            headFunction.disassembleFunction()
            headFunction.printData()
            headFunction = headFunction.nextFunction
        return 0