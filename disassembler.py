#!/usr/bin/env python3

import json
from function import Function
from abi_parser import *
from callgraph import CallFlowGraph
from utils import field_element_repr, PRIME, CFG_NODE_ATTR, CFG_GRAPH_ATTR, CFG_EDGE_ATTR
from graphviz import Digraph
from graphviz import Source

class Disassembler:
    """
    Main class

    loads the cairo json (Bytecode + ABI)
    Analyze and disassemble
    """
    def __init__(self, file, analyze=True):
        self.file = file
        self.functions = []
        self.structs = None
        self.json = None
        self.builtins = []
        self.call_graph = None

        if analyze:
            self.analyze()

    def analyze(self):
        """
        Start the analyze of the code by parsing the cairo/starknet/other json.
        Then it creates every Function class and add it to the Disassembler functions list
        """
        json_data = ""
        with self.file[0] as f:
            json_data = json.load(f)
        
        if (json_data is None or json_data == ""):
            exit(1)
        json_type = detect_type_input_json(json_data)
        self.json = parseToJson(json_data, json_type)
        self.structs = extract_struct(json_type, json_data)
        self.builtins = extract_builtins(json_type, json_data)
        #self.dump_json()

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
                # only for direct call
                if inst.is_call_direct():
                    offset = int(inst.id) - int(field_element_repr(int(inst.imm), PRIME))
                    if (offset < 0):
                        offset = int(inst.id) + int(inst.imm)
                    xref_func = self.get_function_by_offset(str(offset))
                    inst.call_xref_func_name = xref_func.name if xref_func != None else None

    def print_disassembly(self, func_name=None, func_offset=None):
        """
        Iterate over every function and print the disassembly
        """
        if (self.builtins != []):
            print("_" * 50)
        print(self.print_builtins())
        print("_" * 50)
        print(self.print_structs())
        print("_" * 50)
        # Disassembly for all functions
        if (func_name is None and func_offset is None):
            for function in self.functions:
                function.print()

        # func_name or func_offset provided
        else:
            if (func_name is not None):
                function = self.get_function_by_name(func_name)
            elif (func_offset is not None):
                function = self.get_function_by_offset(func_offset)

            if (function != None):
                function.print()
            else:
                print("Error : Function does not exist.")

    def print_structs(self):
        struct_str = ""
        for struct in self.structs:
            struct_str += "\n\t struct: " + struct + "\n"
            for attribut in self.structs[struct]:
                struct_str += "\t    " + self.structs[struct][attribut]["attribut"]
                struct_str += "   : " + self.structs[struct][attribut]["cairo_type"] + "\n"
        return struct_str

    def print_builtins(self):
        builtins_str = ""
        if (self.builtins != []):
            builtins_str += "\n%builtins "
            return builtins_str + ' '.join(self.builtins)
        return builtins_str

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

    def print_cfg(self, func_name=None, func_offset=None, view=True):
        """
        Print the CFG (Control Flow Graph)
        """

        # CFG for all functions
        graph = Digraph(name='CFG (all functions)',
                        node_attr=CFG_NODE_ATTR,
                        graph_attr=CFG_GRAPH_ATTR,
                        edge_attr=CFG_EDGE_ATTR)

        if (func_name is None and func_offset is None):
            for function in self.functions:
                function.generate_cfg()
                graph.subgraph(function.cfg.dot)
            graph.render(directory='output-cfg', view=view)


        # func_name or func_offset provided
        else:
            if (func_name is not None):
                function = self.get_function_by_name(func_name)
            elif (func_offset is not None):
                function = self.get_function_by_offset(func_offset)

            if (function != None):
                function.print_cfg()
            else:
                print("Error : Function does not exist.")

    def analytics(self):
        analytics = {}
        analytics["functions"] = str(len(self.functions))
        analytics["builtins"] = str(len(self.builtins))
        analytics["decorators"] = []
        call = 0
        entry_point = ""
        for function in self.functions:
            if (function.entry_point):
                entry_point = function.name
            for instruction in function.instructions:
                if (instruction.opcode == "CALL"):
                    call += 1
            analytics["decorators"] += function.decorators
        analytics["call_nbr"] = str(call)
        analytics["entry_point"] = entry_point
        #print(json.dumps(analytics, indent=3))
        return analytics
