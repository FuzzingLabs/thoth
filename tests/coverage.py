import glob
import sys
import os, io
from thoth.app.disassembler.disassembler import Disassembler


def disassembler_coverage():
    all_test = glob.glob("./json_files/*")
    for test in all_test:
        with open(test, "r") as file:
            filename = os.path.basename(file.name).split(".")[0]
            disassembler = Disassembler([file])
            disassembler.decompiler()
            disassembler.print_disassembly()
            for function in disassembler.functions:
                disassembler.print_disassembly(func_name=function.name)
                disassembler.print_disassembly(func_offset=function.offset_start)
                disassembler.print_cfg(
                    folder="output_graph",
                    filename=filename + "cfg",
                    view=False,
                    func_name=function.name,
                )
                disassembler.print_cfg(
                    folder="output_graph",
                    filename=filename + "cfg",
                    view=False,
                    func_name=function.offset_start,
                )
                try:
                    disassembler.print_disassembly("toto")
                except BaseException:
                    print("error")
            disassembler.dump_json()
            disassembler.print_call_flow_graph(folder="output_graph", filename=filename, view=True)
            disassembler.print_cfg(folder="output_graph", filename=filename + "cfg", view=True)
            disassembler.analytics()


disassembler_coverage()
