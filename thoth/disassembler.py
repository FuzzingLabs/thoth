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
    extract_labels,
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

    def __init__(self, file, color=False):
        """Init the disassembler object and run the analyzer.

        Args:
            file (file): The smart contract file
            color (bool, optional): Enable or disable coloring of the output. Defaults to False.
        """
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
        self.analyze()

    def analyze(self):
        """Run the analyze of the file.

        Raises:
            SystemExit: If the file provided is an invalid JSON.
            SystemExit: if the JSON is empty.
        """
        json_data = ""
        with self.file[0] as f:
            try:
                json_data = json.load(f)
            except json.decoder.JSONDecodeError:
                raise SystemExit("Error: Provided file is not a valid JSON.")

        # Start parsing the json to extract interesting info
        json_type = detect_type_input_json(json_data)
        self.json = parse_to_json(json_data, json_type)
        self.builtins = extract_builtins(json_type, json_data)
        self.structs = extract_structs(json_type, json_data)
        self.events = extract_events(json_type, json_data)
        self.references = extract_references(json_type, json_data)
        self.hints = extract_hints(json_type, json_data)
        self.prime = extract_prime(json_type, json_data)
        self.labels = extract_labels(json_type, json_data)

        # Create the list of Functions
        for function in self.json:
            offset_start = list(self.json[function]["instruction"].keys())[0]
            offset_end = list(self.json[function]["instruction"].keys())[-1]
            name = function
            instructions = self.json[function]["instruction"]
            args = (
                self.json[function]["data"]["args"]
                if ("args" in self.json[function]["data"])
                else {}
            )
            implicitargs = (
                self.json[function]["data"]["implicitargs"]
                if ("implicitargs" in self.json[function]["data"])
                else {}
            )
            ret = (
                self.json[function]["data"]["return"]
                if ("return" in self.json[function]["data"])
                else {}
            )
            decorators = (
                self.json[function]["data"]["decorators"]
                if ("decorators" in self.json[function]["data"])
                else {}
            )
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
                    self.labels,
                    entry_point=self.json[function]["data"]["entry_point"]
                    if json_type != "get_code"
                    else True,
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
        """Print the disassembly of all the bytecodes or a given function.

        Args:
            func_name (string, optional): The function name to disassemble. Defaults to None.
            func_offset (string, optional): The function offset to disassemble. Defaults to None.

        Raises:
            SystemExit: If the function name or offset does not exist.
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

        elif func_name is None and func_offset is None:
            for function in self.functions:
                function.print()

        else:
            if func_name is not None:
                function = self.get_function_by_name(func_name)
            elif func_offset is not None:
                function = self.get_function_by_offset(func_offset)

            if function is not None:
                function.print()
            else:
                raise SystemExit("Error: Function does not exist.")

    def print_structs(self):
        """Print the structures parsed from the ABI.

        Returns:
            string: Return a string containing the output of the parsed structures.
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
        """Print the events parsed from the ABI.

        Returns:
            string: Return a string containing the output of the parsed events.
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
        """Print the builtins parsed from the ABI.

        Returns:
            string: Return a string containing the output of the parsed builtins.
        """
        builtins_str = ""
        if self.builtins != []:
            builtins_str += "\n\t %builtins "
            return builtins_str + utils.color.RED + " ".join(self.builtins) + utils.color.ENDC
        return builtins_str

    def dump_json(self):
        """Print the JSON containing the datas parsed from the ABI."""
        print("\n", json.dumps(self.json, indent=3))

    def get_function_by_name(self, func_name):
        """Get the function object from it name.

        Args:
            func_name (string): The name of the function to return.

        Returns:
            Function: Function object.
        """
        for function in self.functions:
            if func_name == function.name:
                return function
        return None

    def get_function_by_offset(self, offset):
        """Get the function object from it offset.

        Args:
            func_offset (string): The offset of the function to return.

        Returns:
            Function: Function object.
        """
        for function in self.functions:
            if function.offset_start == offset:
                return function
        return None

    def print_call_flow_graph(self, filename, view=True, format="pdf"):
        """Print the call flow graph.

        Args:
            filename (string): The name of the output file.
            view (bool, optional): Set if the output file should be opened or not. Defaults to True.
            format (str, optional): The format of the output file. Defaults to "pdf".

        Returns:
            dot: The call graph dot.
        """
        if self.call_graph is None:
            self.call_graph = CallFlowGraph(self.functions, filename=filename, format=format)

        self.call_graph.print(view)
        return self.call_graph.dot

    def print_cfg(self, filename, format="pdf", func_name=None, func_offset=None, view=True):
        """Print the CFG.

        Args:
            filename (string): The name of the output file.
            format (str, optional): The format of the output file. Defaults to "pdf".
            func_name (string, optional): Build the CFG of the given function name. Defaults to None.
            func_offset (string, optional): Build the CFG of the given function offset. Defaults to None.
            view (bool, optional): Set if the output file should be opened or not. Defaults to True.
        """
        graph = Digraph(
            name=filename,
            node_attr=CFG_NODE_ATTR,
            graph_attr=CFG_GRAPH_ATTR,
            edge_attr=CFG_EDGE_ATTR,
        )
        graph.format = format
        if func_name is None and func_offset is None:
            for function in self.functions:
                function.generate_cfg()
                graph.subgraph(function.cfg.dot)
            graph.render(directory="output-cfg", view=view)

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
        """Analyze and get some datas for unit tests.

        Returns:
            Dictionnary: Dictionnary containings datas.
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
        analytics["structs"] = len(self.structs)
        # print(json.dumps(analytics, indent=3))
        return analytics
