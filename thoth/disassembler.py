#!/usr/bin/env python3

import json

from graphviz import Digraph
from thoth import utils
from .abi_parser import (
    detect_type_input_json,
    extract_hints,
    parse_to_json,
    extract_events,
    extract_structs,
    extract_builtins,
    extract_prime,
    extract_references,
)
from .callgraph import CallFlowGraph
from .utils import CFG_NODE_ATTR, CFG_GRAPH_ATTR, CFG_EDGE_ATTR, DEFAULT_PRIME
from .function import Function


class Disassembler:
    """
    Main class

    loads the cairo json (Bytecode + ABI)
    Analyze and disassemble
    """

    def __init__(self, file, analyze=True, color=False):
        self.file = file
        self.json = None
        self.functions = []
        self.builtins = []
        self.structs = {}
        self.events = {}
        self.call_graph = None
        self.prime = None
        utils.globals()
        utils.color = utils.bcolors(color=color)
        if analyze:
            self.analyze()

    def analyze(self):
        """
        Start the analyze of the code by parsing the cairo/starknet/other json.
        Then it creates every Function class and add it to the Disassembler functions list
        """
        json_data = ""
        with self.file[0] as f:
            try:
                json_data = json.load(f)
            except json.decoder.JSONDecodeError:
                raise SystemExit("Error: Provided file is not a valid JSON.")
        # Check the file is OK
        if json_data is None or json_data == "":
            raise SystemExit("Error: The provided JSON is empty")

        # Start parsing the json to extract interesting info
        json_type = detect_type_input_json(json_data)
        self.json = parse_to_json(json_data, json_type)
        self.builtins = extract_builtins(json_type, json_data)
        self.structs = extract_structs(json_type, json_data)
        self.events = extract_events(json_type, json_data)
        self.references = extract_references(json_type, json_data)
        self.hints = extract_hints(json_type, json_data)
        self.prime = extract_prime(json_type, json_data)

        # Create the list of Functions
        for function in self.json:
            offset_start = list(self.json[function]["instruction"].keys())[0]
            offset_end = list(self.json[function]["instruction"].keys())[-1]
            name = function
            instructions = self.json[function]["instruction"]
            args = self.json[function]["data"]["args"] if ("args" in self.json[function]["data"]) else {}
            implicitargs = self.json[function]["data"]["implicitargs"] if ("implicitargs" in self.json[function]["data"]) else {}
            ret = self.json[function]["data"]["return"] if ("return" in self.json[function]["data"]) else {}
            decorators = self.json[function]["data"]["decorators"] if ("decorators" in self.json[function]["data"]) else {}
            self.functions.append(
                Function(
                    self.prime,
                    offset_start,
                    offset_end,
                    name,
                    instructions,
                    args,
                    implicitargs,
                    ret,
                    decorators,
                    entry_point=self.json[function]["data"]["entry_point"] if json_type != "get_code" else True,
                    is_import=not name.startswith("__"),
                )
            )
        # Analyze all the CALL to find the corresponding function, also set the references and hints to their instructions
        for func in self.functions:
            for inst in func.instructions:
                # Only for direct call
                if inst.is_call_direct():
                    xref_func = self.get_function_by_offset(str(inst.call_offset))
                    inst.call_xref_func_name = xref_func.name if xref_func is not None else None
                if inst.id in self.references:
                    inst.ref = self.references[inst.id]
                if inst.id in self.hints:
                    inst.hint = self.hints[inst.id]

    def print_disassembly(self, func_name=None, func_offset=None):
        """
        Iterate over every function and print the disassembly
        """
        if self.builtins:
            print("_" * 75)
            print(self.print_builtins())
        if self.structs:
            print("_" * 75)
            print(self.print_structs())
        if self.events:
            print("_" * 75)
            print(self.print_events())
        print("_" * 75)

        if self.functions == []:
            return

        # Disassembly for all functions
        elif func_name is None and func_offset is None:
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
                raise SystemExit("Error: Function does not exist.")

    def print_structs(self):
        """
        Print the structures
        """
        struct_str = ""
        for struct in self.structs:
            struct_str += "\n\t struct: " + utils.color.BEIGE + struct + utils.color.ENDC + "\n"
            for attribut in self.structs[struct]:
                struct_str += (
                    "\t    "
                    + utils.color.GREEN
                    + self.structs[struct][attribut]["attribut"]
                    + utils.color.ENDC
                )
                struct_str += (
                    "   : "
                    + utils.color.YELLOW
                    + self.structs[struct][attribut]["cairo_type"]
                    + utils.color.ENDC
                    + "\n"
                )
        return struct_str

    def print_events(self):
        """
        Print the events
        """
        events_str = ""
        for event_name, data in self.events.items():
            events_str += "\n\t event: " + utils.color.BEIGE + event_name + utils.color.ENDC + "\n"
            for attribut in data:
                events_str += "\t    " + utils.color.GREEN + attribut["name"] + utils.color.ENDC
                events_str += (
                    "   : " + utils.color.YELLOW + attribut["type"] + utils.color.ENDC + "\n"
                )
        return events_str

    def print_builtins(self):
        """
        Print the builtins
        """
        builtins_str = ""
        if self.builtins != []:
            builtins_str += "\n\t %builtins "
            return builtins_str + utils.color.RED + " ".join(self.builtins) + utils.color.ENDC
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
        graph = Digraph(
            name=filename,
            node_attr=CFG_NODE_ATTR,
            graph_attr=CFG_GRAPH_ATTR,
            edge_attr=CFG_EDGE_ATTR,
        )
        graph.format = format
        # The graph will contains all functions
        if func_name is None and func_offset is None:
            for function in self.functions:
                function.generate_cfg()
                graph.subgraph(function.cfg.dot)
            graph.render(directory="output-cfg", view=view)

        # Only `func_name` or `func_offset` will be in the graph
        else:
            if func_name is not None:
                function = self.get_function_by_name(func_name)
            elif func_offset is not None:
                function = self.get_function_by_offset(func_offset)

            if function is not None:
                function.generate_cfg()
                graph.subgraph(function.cfg.dot)
                graph.render(directory="output-cfg", view=view)
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
        # print(json.dumps(analytics, indent=3))
        return analytics
