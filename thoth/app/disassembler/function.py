from graphviz import Digraph
from typing import List
from thoth.app import utils
from thoth.app.cfg.cfg import CFG
from thoth.app.disassembler.instruction import Instruction


class Function:
    """The function class"""

    def __init__(
        self,
        prime: int,
        offset_start: int,
        offset_end: int,
        name: str,
        instructions: Instruction,
        args: dict,
        implicitargs: dict,
        ret: dict,
        decorators: List,
        labels: dict,
        is_import: bool = False,
        entry_point: bool = False,
    ) -> None:
        """Create the function object

        Args:
            prime (Int): The prime number
            offset_start (String): The offset where the function start
            offset_end (String): The offset where the function end
            name (String): The function name
            instructions (List): List of the instructions
            args (Dictionnary): Dict containing the arguments
            implicitargs (Dictionnary): Dict containing the implicit arguments
            ret (Dictionnary): Dict containing the return
            decorators (List): Dict containing the decorators
            labels (Dictionnary): Dictionary containing the labels
            is_import (bool, optional): Set to true if the function is an import. Defaults to False.
            entry_point (bool, optional): Set to true if the function is an entry_point. Defaults to False.
        """
        self.prime = prime
        self.offset_start = offset_start
        self.offset_end = offset_end
        self.name = name
        self.instructions_dict = instructions
        self.instructions: List = []
        self.args = args if args != {} else None
        self.implicitargs = implicitargs if implicitargs != {} else None
        self.ret = ret if ret != {} else None
        self.decorators = decorators
        self.is_import = is_import
        self.entry_point = entry_point
        self.cfg = None
        self.labels = labels
        self._generate_instruction()

    def _generate_instruction(self) -> List[Instruction]:
        """Create a list of the instruction with its datas

        Returns:
            List: List of instructions
        """
        for offset in self.instructions_dict:
            for bytecode in self.instructions_dict[offset]:
                self.instructions.append(
                    Instruction(
                        offset,
                        self.instructions_dict[offset][bytecode],
                        self.prime,
                        self.labels,
                    )
                )
        return self.instructions

    def get_prototype(self) -> str:
        """Build the string of the prototype

        Returns:
            String: The string of the prototype
        """
        prototype = ""
        for decorator in self.decorators:
            prototype += f"@{decorator} "
        prototype += f"func {self.name}"
        datas = [
            ("implicitargs", self.implicitargs),
            ("args", self.args),
            ("ret", self.ret),
        ]
        for data in datas:
            data_name = data[0]
            data_content = data[1]
            prototype += (
                " -> ("
                if data_name == "ret" and data_content is not None
                else "("
                if data_name == "args"
                else "{"
                if data_name == "implicitargs"
                else ""
            )
            if data_content is not None:
                for idarg in data_content:
                    if data_content[idarg] != {}:
                        for args in data_content[idarg]:
                            prototype += args + " : " + data_content[idarg][args]
                            if int(idarg) != len(data_content) - 1:
                                prototype += ", "
            prototype += (
                ")"
                if (data_name == "args" or (data_name == "ret" and data_content is not None))
                else "}"
                if data_name == "implicitargs"
                else ""
            )
        return prototype

    def arguments_list(self) -> List[str]:
        """
        Return:
            function_arguments (list): a list of the function arguments (implicits or not) and return values names
        """
        function_arguments = []

        # Merge implicitargs, args and ret 
        arguments_list = []
        for dict in (self.args, self.implicitargs, self.ret):
            if dict is not None:
                arguments_list.append(dict)

        # Get arguments names
        for argument in arguments_list:
            for _ in [*argument.values()]:
                function_arguments.append([*_.keys()][0])
        return function_arguments

    def print(self) -> None:
        """
        Iterate over each instruction and print the disassembly
        """
        prototype = self.get_prototype()
        print(f"\n\t{utils.color.BLUE + prototype + utils.color.ENDC}")
        for instr in self.instructions:
            print(instr.print(), end="")
        print()

    def generate_cfg(self) -> None:
        """Generate the CFG"""
        self.cfg = CFG(self.name, self.instructions)

    def print_cfg(self, view: bool = True) -> Digraph:
        """Print the dot

        Args:
            view (bool, optional): Set if the disassembler should open the output file or not. Defaults to True.

        Returns:
            Dot: the output Dot
        """
        # The CFG is not generated yet
        if self.cfg is None:
            self.generate_cfg()

        # Show/Render the CFG
        self.cfg.print(view)
        return self.cfg.dot
