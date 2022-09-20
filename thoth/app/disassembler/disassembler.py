#!/usr/bin/env python3

import json
from optparse import Option

from graphviz import Digraph
from typing import IO, Optional
from thoth import utils
from thoth.app.disassembler.abi_parser import (
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
from thoth.app.decompiler.decompiler import Decompiler
from thoth.app.cfg.callgraph import CallFlowGraph
from thoth.app.cfg.utils import CFG_NODE_ATTR, CFG_GRAPH_ATTR, CFG_EDGE_ATTR, DEFAULT_PRIME
from thoth.app.decompiler.function import Function


class Disassembler:
    """
    Main class

    loads the cairo json (Bytecode + ABI)
    Analyze and disassemble
    """

    def __init__(self, file: IO, color: bool = False) -> None:
        """Init the disassembler object and run the analyzer.

        Args:
            file (file): The smart contract file
            color (bool): Enable or disable coloring of the output. Defaults to False.
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

    def analyze(self) -> None:
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
                    xref_func = self.get_function_by_offset(
                        str(inst.call_offset)
                    )
                    inst.call_xref_function_name = (
                        xref_func.name if xref_func is not None else None
                    )
                if inst.id in self.references:
                    inst.ref = self.references[inst.id]
                if inst.id in self.hints:
                    inst.hint = self.hints[inst.id]

    def print_disassembly(self, function_name: Optional[str] = None, function_offset: Optional[str] = None) -> None:
        """Print the disassembly of all the bytecodes or a given function.

        Args:
            function_name (string, optional): The function name to disassemble. Defaults to None.
            function_offset (string, optional): The function offset to disassemble. Defaults to None.

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

        elif function_name is None and function_offset is None:
            for function in self.functions:
                function.print()

        else:
            if function_name is not None:
                function = self.get_function_by_name(function_name)
            elif function_offset is not None:
                function = self.get_function_by_offset(function_offset)

            if function is not None:
                function.print()
            else:
                raise SystemExit("Error: Function does not exist.")

    def print_structs(self, decompiler: bool = False) -> str:
        """Print the structures parsed from the ABI.

        Args:
            decompiler (bool): decompile the struct 
        Returns:
            string: Return a string containing the output of the parsed structures.
        """
        parsed_string = ""

        for struct in self.structs:
            if decompiler == True and len(self.structs[struct]) == 0:
                continue
            parsed_string += (
                "struct "
                + utils.color.BEIGE
                + struct
                + utils.color.ENDC
                + ":\n"
            )
            for attribut in self.structs[struct]:
                parsed_string += (
                    "\tmember "
                    + utils.color.GREEN
                    + self.structs[struct][attribut]["attribut"]
                    + utils.color.ENDC
                )
                parsed_string += (
                    " : "
                    + utils.color.YELLOW
                    + self.structs[struct][attribut]["cairo_type"]
                    + utils.color.ENDC
                    + "\n"
                )
            parsed_string += "end\n\n"
        return parsed_string

    def print_events(self) -> str:
        """Print the events parsed from the ABI.

        Returns:
            string: Return a string containing the output of the parsed events.
        """
        events = ""
        for event_name, data in self.events.items():
            events += (
                "\n\t event: "
                + utils.color.BEIGE
                + event_name
                + utils.color.ENDC
                + "\n"
            )
            for attribut in data:
                events += (
                    "\t    "
                    + utils.color.GREEN
                    + attribut["name"]
                    + utils.color.ENDC
                )
                events += (
                    "   : "
                    + utils.color.YELLOW
                    + attribut["type"]
                    + utils.color.ENDC
                    + "\n"
                )
        return events

    def print_builtins(self) -> str:
        """Print the builtins parsed from the ABI.

        Returns:
            string: Return a string containing the output of the parsed builtins.
        """
        builtins = ""
        if self.builtins != []:
            builtins += "\n%builtins "
            return (
                builtins
                + utils.color.RED
                + " ".join(self.builtins)
                + utils.color.ENDC
            )
        return builtins

    def dump_json(self) -> None:
        """Print the JSON containing the datas parsed from the ABI."""
        print("\n", json.dumps(self.json, indent=3))

    def get_function_by_name(self, function_name: str) -> Optional[Function]:
        """Get the function object from it name.

        Args:
            function_name (string): The name of the function to return.

        Returns:
            Function: Function object.
        """
        for function in self.functions:
            if function_name == function.name:
                return function
        return None

    def get_function_by_offset(self, offset: str) -> Optional[Function]:
        """Get the function object from it offset.

        Args:
            function_offset (string): The offset of the function to return.

        Returns:
            Function: Function object.
        """
        for function in self.functions:
            if function.offset_start == offset:
                return function
        return None

    def print_call_flow_graph(self, filename: str, view: bool = True, format: str = "pdf") -> Digraph:
        """Print the call flow graph.

        Args:
            filename (string): The name of the output file.
            view (bool, optional): Set if the output file should be opened or not. Defaults to True.
            format (str, optional): The format of the output file. Defaults to "pdf".

        Returns:
            dot: The call graph dot.
        """
        if self.call_graph is None:
            self.call_graph = CallFlowGraph(
                self.functions, filename=filename, format=format
            )

        self.call_graph.print(view)
        return self.call_graph.dot

    def print_cfg(
        self,
        filename: str,
        format: str = "pdf",
        function_name: Optional[str] = None,
        function_offset: Optional[str] = None,
        view: bool = True,
    ) -> None:
        """Print the CFG.

        Args:
            filename (string): The name of the output file.
            format (str, optional): The format of the output file. Defaults to "pdf".
            function_name (string, optional): Build the CFG of the given function name. Defaults to None.
            function_offset (string, optional): Build the CFG of the given function offset. Defaults to None.
            view (bool, optional): Set if the output file should be opened or not. Defaults to True.
        """
        graph = Digraph(
            name=filename,
            node_attr=CFG_NODE_ATTR,
            graph_attr=CFG_GRAPH_ATTR,
            edge_attr=CFG_EDGE_ATTR,
        )
        graph.format = format
        if function_name is None and function_offset is None:
            for function in self.functions:
                function.generate_cfg()
                graph.subgraph(function.cfg.dot)
            graph.render(directory="output-cfg", view=view)

        else:
            if function_name is not None:
                function = self.get_function_by_name(function_name)
            elif function_offset is not None:
                function = self.get_function_by_offset(function_offset)

            if function is not None:
                function.generate_cfg()
                graph.subgraph(function.cfg.dot)
                graph.render(directory="output-cfg", view=view)
            else:
                print("Error : Function does not exist.")

    def analytics(self) -> dict:
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

    def decompiler(self) -> None:
        """
        Decompile the functions
        """
        print(self.print_builtins())
        for function in self.functions:
            if function.is_import:
                function_name = function.name.split(".")[-1]
                package = ".".join(function.name.split(".")[:-1])
                print(f"from {package} import {function_name}")
        print(self.print_structs(decompiler=True))
        decomp = Decompiler(functions=self.functions)
        print(decomp.decompile_code())
