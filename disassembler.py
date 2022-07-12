#!/usr/bin/env python3

import json
from graphviz import Digraph

from function import Function
from utils import format_print, OPERATORS, PRIME
from jsonParser import *

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
        self.cfg = None

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

    def print(self, func_name=None):
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

    def _call_flow_graph_generate_nodes(self):
        """
        Create all the function nodes
        """

        # TODO - add entrypoint info
        # TODO - add import info
        for function in self.functions:

            # default shape
            shape = 'oval'

            # This function is an entrypoint
            if function.entry_point:
                shape = 'doubleoctagon'

            self.call_graph.node(function.offset_start,
                                 label=function.name,
                                 shape=shape)
        

    def _generate_call_flow_graph(self):
        """
        Create all the function Node for the CallFlowGraph and call _generate_call_flow_graph_edges to build the edges
        """
        self.call_graph = Digraph('CALL FLOW GRAPH', comment='CALL FLOW GRAPH')
        
        # First, we create the nodes
        self._call_flow_graph_generate_nodes()

        edgesDone = []
        # build the edges btw function (nodes)
        for function in self.functions:
            for instr in function.instructions:
                if ("CALL" in instr.opcode):
                    offset = int(instr.id) - (PRIME - int(instr.imm))
                    if (offset < 0):
                        offset = int(instr.id) + int(instr.imm)
                    if (str(offset) != function.offset_start and (function.offset_start, str(offset)) not in edgesDone):
                        edgesDone.append((function.offset_start, str(offset)))
                        self.call_graph.edge(function.offset_start, str(offset))


    def print_call_flow_graph(self, view=True):
        """
        Print the CallFlowGraph
        """

        # call flow graph not generated yet
        if (self.call_graph == None):
            self._generate_call_flow_graph()

        # show the call flow graph
        self.call_graph.render(directory='doctest-output', view=view)
        return self.call_graph

    def print_cfg(self):
        """
        Print the CFG (Control Flow Graph)
        """

        print("TODO CFG")
        raise NotImplementedError
