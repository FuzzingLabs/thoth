from instruction import Instruction
from utils import format_print
from cfg import CFG

class Function:
    """
    Function Class
    """
    def __init__(self, offset_start, offset_end, name, instructions, args, ret, decorators, is_import=False, entry_point=False) -> None:
        self.offset_start = offset_start
        self.offset_end = offset_end
        self.name = name
        self.instructions_dict = instructions
        self.instructions = []
        self.args = args if args != {} else None
        self.ret = ret if ret != {} else None
        self.decorators = decorators
        self.is_import = is_import
        self.entry_point = entry_point
        self.cfg = None

        self._generate_instruction()

    def _generate_instruction(self):
        """
        Create a list of the instruction with its datas
        """
        for offset in self.instructions_dict:
            for bytecode in self.instructions_dict[offset]:
                    self.instructions.append(Instruction(offset, self.instructions_dict[offset][bytecode]))
        return self.instructions
    
    def get_prototype(self):
        """
        Build the string of the prototype
        """
        prototype = ""
        for decorator in self.decorators:
            prototype += f"@{decorator} "
        prototype += f"func {self.name}("
        if (self.args != None):
            for idarg in self.args:
                if (self.args[idarg] != {}):
                    for args in self.args[idarg]:
                        prototype += args
                        prototype +=" : "
                        prototype += self.args[idarg][args] + " "
                        if (int(idarg) != len(self.args) - 1):
                            prototype += ", "
        prototype += ")"
        if (self.ret != None):
            prototype += " -> ("
            for idarg in self.ret:
                if (self.ret[idarg] != {}):
                    for args in self.ret[idarg]:
                        prototype += args
                        prototype +=" : "
                        prototype += self.ret[idarg][args]
                        if (int(idarg) != len(self.ret) - 1):
                            prototype += ", "
                        else:
                            prototype += ")"
        return prototype

    def print(self):
        """
        Iterate over each instruction and print the disassembly
        """
        prototype = self.get_prototype()
        print(f"\n\t{prototype}\n")
        for instr in self.instructions:
            instr.print()

    def print_cfg(self, view=True):
        """
        Print the CFG
        """

        # call flow graph not generated yet
        if (self.cfg == None):
            self.cfg = CFG(self.instructions)

        # show the call flow graph
        self.cfg.print(view)
        return self.cfg.dot