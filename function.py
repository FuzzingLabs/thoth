from instruction import Instruction
from utils import format_print
from cfg import CFG

class Function:
    """
    Function Class
    """
    def __init__(self, offset_start, offset_end, name, instructions, args,  implicitargs,ret, decorators, is_import=False, entry_point=False) -> None:
        self.offset_start = offset_start
        self.offset_end = offset_end
        self.name = name
        self.instructions_dict = instructions
        self.instructions = []
        self.args = args if args != {} else None
        self.implicitargs = implicitargs if implicitargs != {} else None
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
        prototype += f"func {self.name}"
        datas = [("implicitargs", self.implicitargs), ("args", self.args), ("ret", self.ret)]
        
        for data in datas:
            data_name = data[0]
            data_content = data[1]
            prototype += " -> (" if data_name == "ret" and data_content != None \
                        else "(" if data_name == "args" \
                        else "{" if data_name == "implicitargs" \
                        else ""
            if (data_content != None):
                for idarg in data_content:
                    if (data_content[idarg] != {}):
                        for args in data_content[idarg]:
                            prototype += args + " : " + data_content[idarg][args] + " "
                            if (int(idarg) != len(data_content) - 1):
                                prototype += ", "
            prototype += ")" if data_name == "args" else "}" if data_name == "implicitargs" else ""
        return prototype

    def print(self):
        """
        Iterate over each instruction and print the disassembly
        """
        prototype = self.get_prototype()
        print(f"\n\t{prototype}\n")
        for instr in self.instructions:
            print(instr.print())

    def print_cfg(self, dot):
        """
        Print the CFG
        """
        # call flow graph not generated yet
        if (self.cfg == None):
            self.cfg = CFG(self.instructions, dot)
        return self.cfg.dot