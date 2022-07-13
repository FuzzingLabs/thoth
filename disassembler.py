#!/usr/bin/env python3

import json
from function import Function

from jsonParser import *
from callgraph import CallGraph

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
            ret = self.json[function]["data"]["return"]
            decorators = self.json[function]["data"]["decorators"]

            self.functions.append(
                Function(offset_start,
                         offset_end,
                         name, 
                         instructions, 
                         args, 
                         ret, 
                         decorators,
                         entry_point=self.json[function]["data"]["entry_point"]))
        
        return self.functions

    def print_disassembly(self, func_name=None):
        """
        Iterate over every function and print the disassembly
        """
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
            if (function.offset_start == offset):
                return function
        return None

    
    def print_call_flow_graph(self, view=True):
        """
        Print the CallFlowGraph
        """

        # call flow graph not generated yet
        if (self.call_graph == None):
            self.call_graph = CallGraph(self.functions)

        # show the call flow graph
        self.call_graph.print(view)
        return self.call_graph.dot

    def print_cfg(self, func_name=None):
        """
        Print the CFG (Control Flow Graph)
        """

        # TODO - add func_offset option

        if (func_name is None):
            for function in self.functions:
                function.print_cfg()
        else:
            function = self.get_function_by_name(func_name)
            if (function != None):
                function.print_cfg()
            else:
                print("Error : Function does not exist.")
