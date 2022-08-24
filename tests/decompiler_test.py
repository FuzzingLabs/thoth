import glob
import sys
import os
from thoth.disassembler import Disassembler


def main():
    all_test = glob.glob("./json_files/*")
    for test in all_test:
        with open(test, "r") as file:
            disassembler = Disassembler([file])
            disassembler.decompiler_poc()


main()
