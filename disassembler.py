#!/usr/bin/env python3

import sys
import json
from turtle import color
import utils
from graphviz import Digraph

from abi_parser import detect_type_input_json, parse_to_json, extract_struct, extract_builtins, extract_prime
from callgraph import CallFlowGraph
from utils import CFG_NODE_ATTR, CFG_GRAPH_ATTR, CFG_EDGE_ATTR
from function import Function

# Default prime value
DEFAULT_PRIME = (2**251) + (17 * (2**192)) + 1

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
        self.prime = None

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

        # Check the file is OK
        if (json_data is None or json_data == ""):
            print("Error: The provided JSON is empty")
            sys.exit(1)

        # Start parsing the json to extract interesting info
        json_type = detect_type_input_json(json_data)
        self.json = parse_to_json(json_data, json_type)
        self.structs = extract_struct(json_type, json_data)
        self.builtins = extract_builtins(json_type, json_data)
        self.prime = extract_prime(json_type, json_data) if not None else DEFAULT_PRIME
        # self.dump_json()

        # Create the list of Functions
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
                Function(self.prime,
                         offset_start,
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

        # Analyze all the CALL to find the corresponding function
        for func in self.functions:
            for inst in func.instructions:
                # Only for direct call
                if inst.is_call_direct():
                    xref_func = self.get_function_by_offset(str(inst.call_offset))
                    inst.call_xref_func_name = xref_func.name if xref_func is not None else None

    def print_disassembly(self, func_name=None, func_offset=None):
        """
        Iterate over every function and print the disassembly
        """
        if self.builtins != []:
            print("_" * 75)
        print(self.print_builtins())
        print("_" * 75)
        print(self.print_structs())
        print("_" * 75)

        if self.functions == []:
            print()
            print("No bytecode/functions found (maybe it's a contract interface?)")
            print("Otherwise please open an issue, Thanks!")
            print()
            sys.exit(1)

        # Disassembly for all functions
        elif (func_name is None and func_offset is None):
            for function in self.functions:
                function.print()

        # func_name or func_offset provided
        else:
            if func_name is not None:
                function = self.get_function_by_name(func_name)
            elif func_offset is not None:
                function = self.get_function_by_offset(func_offset)

            # Print the function
            if function is not None:
                function.print()
            else:
                print("Error: Function does not exist.")
                sys.exit(1)

    def print_structs(self):
        """
        Print the structures
        """
        struct_str = ""
        for struct in self.structs:
            struct_str += "\n\t struct: " + utils.color.BEIGE + struct + utils.color.ENDC + "\n"
            for attribut in self.structs[struct]:
                struct_str += "\t    " + utils.color.GREEN + self.structs[struct][attribut]["attribut"] + utils.color.ENDC
                struct_str += "   : " + utils.color.YELLOW + self.structs[struct][attribut]["cairo_type"] + utils.color.ENDC + "\n"
        return struct_str

    def print_builtins(self):
        """
        Print the builtins
        """
        builtins_str = ""
        if self.builtins != []:
            builtins_str += "\n\t %builtins "
            return builtins_str + utils.color.YELLOW + ' '.join(self.builtins) + utils.color.ENDC
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
            if func_name == function.name:
                return function
        return None

    def get_function_by_offset(self, offset):
        """
        Return a Function if the offset match
        """
        for function in self.functions:
            if function.offset_start == offset:
                return function
        return None

    def print_call_flow_graph(self, filename, view=True, format="pdf"):
        """
        Print the CallFlowGraph
        """
        # The CallFlowGraph is not generated yet
        if self.call_graph is None:
            self.call_graph = CallFlowGraph(self.functions, filename=filename, format=format)

        # Show/Render the CallFlowGraph
        self.call_graph.print(view)
        return self.call_graph.dot

    def print_cfg(self, filename, format="pdf", func_name=None, func_offset=None, view=True):
        """
        Print the CFG (Control Flow Graph)
        """
        # Create a dot graph
        graph = Digraph(name=filename,
                        node_attr=CFG_NODE_ATTR,
                        graph_attr=CFG_GRAPH_ATTR,
                        edge_attr=CFG_EDGE_ATTR)
        graph.format = format
        # The graph will contains all functions
        if (func_name is None and func_offset is None):
            for function in self.functions:
                function.generate_cfg()
                graph.subgraph(function.cfg.dot)
            graph.render(directory='output-cfg', view=view)


        # Only `func_name` or `func_offset` will be in the graph
        else:
            if func_name is not None:
                function = self.get_function_by_name(func_name)
            elif func_offset is not None:
                function = self.get_function_by_offset(func_offset)

            if function is not None:
                function.print_cfg()
            else:
                print("Error : Function does not exist.")

    def analytics(self):
        """
        Print some interesting metrics
        (Useful for tests as well)
        """
        analytics = {}
        analytics["functions"] = str(len(self.functions))
        analytics["builtins"] = str(len(self.builtins))
        analytics["decorators"] = []
        call = 0
        analytics["entry_point"] = []
        for function in self.functions:
            if function.entry_point:
                analytics["entry_point"].append(function.name)
            for instruction in function.instructions:
                if instruction.opcode == "CALL":
                    call += 1
            analytics["decorators"] += function.decorators
        analytics["call_nbr"] = str(call)
        #print(json.dumps(analytics, indent=3))
        return analytics
