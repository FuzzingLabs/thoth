#!/usr/bin/env python3

import json
from function import Function
from graphviz import Digraph
from jsonParser import *
from callgraph import CallFlowGraph
from utils import PRIME

class Disassembler:
    """
    Main class

    loads the cairo json (Bytecode + ABI)
    Analyze and disassemble
    """
    def __init__(self, file, analyze=True):
        self.file = file
        self.functions = []
        self.json = None
        self.call_graph = None

        if analyze:
            self.analyze()

    def analyze(self):
        """
        Start the analyze of the code by parsing the cairo/starknet/other json.
        Then it creates every Function class and add it to the Disassembler functions list
        """
        self.json = parseToJson(self.file)
        
        self.dump_json()

        for function in self.json:
            offset_start = list(self.json[function]["instruction"].keys())[0]
            offset_end = list(self.json[function]["instruction"].keys())[-1]
            name = function
            instructions = self.json[function]["instruction"]
            args = self.json[function]["data"]["args"]
            implicitargs = self.json[function]["data"]["implicitargs"]
            ret = self.json[function]["data"]["return"]
            decorators = self.json[function]["data"]["decorators"]

            self.functions.append(
                Function(offset_start,
                         offset_end,
                         name, 
                         instructions, 
                         args,
                         implicitargs,
                         ret, 
                         decorators,
                         entry_point=self.json[function]["data"]["entry_point"],
                         is_import=not name.startswith('__'))
            )

        # we can now analyze all the CALL to find the corresponding function
        for func in self.functions:
            for inst in func.instructions:
                if ("CALL" in inst.opcode):
                    offset = int(inst.id) - (PRIME - int(inst.imm))
                    if (offset < 0):
                        offset = int(inst.id) + int(inst.imm)
                    xref_func = self.get_function_by_offset(str(offset))
                    #print(xref_func)
                    inst.call_xref_func_name = xref_func.name if xref_func != None else None


    def print_disassembly(self, func_name=None, func_offset=None):
        """
        Iterate over every function and print the disassembly
        """

        # TODO - add func_offset option

        if (func_name is None):
            for function in self.functions:
                function.print()
        else:
            function = self.get_function_by_name(func_name)
            if (function != None):
                function.print()
            else:
                print("Error : Function does not exist.")

    def dump_json(self):
        """
        Print the JSON that contains the informations about functions/instructions/opcode ...
        """
        print("\n", json.dumps(self.json, indent=3))

    def get_function_by_name(self, func_name):
        """
        Return a Function if the func_name match
        """
        for function in self.functions:
            if (func_name == function.name):
                return function
        return None

    def get_function_by_offset(self, offset):
        """
        Return a Function if the offset match
        """
        for function in self.functions:
            #print(function.offset_start)
            #print(offset)
            if (function.offset_start == offset):
                return function
        return None

    
    def print_call_flow_graph(self, view=True):
        """
        Print the CallFlowGraph
        """

        # call flow graph not generated yet
        if (self.call_graph == None):
            self.call_graph = CallFlowGraph(self.functions)

        # show the call flow graph
        self.call_graph.print(view)
        return self.call_graph.dot

    def print_cfg(self, func_name=None):
        """
        Print the CFG (Control Flow Graph)
        """

        # TODO - add func_offset option
        # TODO - generate one big cfg for all function if func_name/func_offset not specified
        dot = Digraph('CFG', comment='CFG')
        if (func_name is None):
            for function in self.functions:
                function.print_cfg(dot)
        else:
            function = self.get_function_by_name(func_name)
            if (function != None):
                function.print_cfg(dot)
            else:
                print("Error : Function does not exist.")
        dot.render(directory='doctest-output', view=True)
