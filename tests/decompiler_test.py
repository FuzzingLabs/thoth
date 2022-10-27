from fileinput import filename
import glob
import sys, io
from thoth.app.disassembler.disassembler import Disassembler
from difflib import SequenceMatcher
from pathlib import Path


def main():
    all_test = glob.glob("./json_files/*")
    old_stdout = sys.stdout
    total = 0
    tests = 0
    for test in all_test:
        new_stdout = io.StringIO()
        sys.stdout = new_stdout
        with open(test, "r") as file:
            filename = Path(test).stem
            try:
                f = open(f"./cairo_files/{filename}.cairo")
            except Exception:
                continue
            content_file = f.readlines()
            f.close()
            disassembler = Disassembler([file])
            disassembler.decompiler_poc()
            output = new_stdout.getvalue()
            sys.stdout = old_stdout
            ratio = SequenceMatcher(None, output, content_file).ratio()
            total += ratio
            tests += 1
            print(f"test {filename} -- simillarity -- {ratio}")
    print("Average simillarity ratio : ", total / tests)


main()
