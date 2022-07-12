from instruction import Instruction
from utils import format_print


class Function:
   """
   Function Class
   """
   def __init__(self, offset_start, offset_end, name, instructions, args, ret, decorators, analyze=True) -> None:
      self.offset_start = offset_start
      self.offset_end = offset_end
      self.name = name
      self.instructions = instructions
      self.args = args if args != {} else None
      self.ret = ret if ret != {} else None
      self.decorators = decorators
      self.instruction_data = None
      self.nextFunction = None
      self.entry_point = False

   def disassemble_function(self):
      """
      Create a linked list of the instruction with it datas
      """
      instructions = self.instructions
      head = None
      previous = None
      instruction_data = None
      for offset in instructions:
         for bytecode in instructions[offset]:
               instruction_data = Instruction(instructions[offset][bytecode], offset)
         if (not head):
               head = instruction_data
         if (previous):
               previous.nextInstruction = instruction_data
         previous = instruction_data
      self.instruction_data = head
   
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
      prototype += ":"
      return prototype

   def print(self):
      """
      Iterate over each instruction and print the disassembly
      """
      instruction_data = self.instruction_data
      prototype = self.get_prototype()
      print(f"\n\t\t{prototype}\n")
      while instruction_data:
         instruction_data.print()
         instruction_data = instruction_data.nextInstruction