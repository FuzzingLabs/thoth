import imp
import graphviz
import re
from disassembler import analyzeGetFunctions
from utils import *
from jsonParser import *

class Disassembler:
   def __init__(self, file):
      self.file = file
      self.functions = []
      self.json = None
      self.dot = None
      self.analyze()

   def analyze(self):
      self.json = parseToJson(self.file)
      headFunction = analyzeGetFunctions(self.json)
      while (headFunction):
         headFunction.disassembleFunction()
         self.functions.append(headFunction)
         headFunction = headFunction.nextFunction
      return self.functions

   def printDisass(self, functionName=None):
      if (functionName is None):
         for function in self.functions:
            function.printData()
      else:
         function = self.getFunctionByName(functionName)
         if (function != None):
            function.printData()
         else:
            print("Error : Function does not exist.")

   def dumpJson(self):
      print("\n", json.dumps(self.json, indent=3))

   def getFunctionByName(self, functionName):
      for function in self.functions:
         if (functionName == function.name):
            return function
      return None

   def getFunctionAtOffset(self, offset):
      for function in self.functions:
         if (function.offsetStart == offset):
            return function
      return None

   def buildCallFlowGraph(self, dot, function, edgesDone):
      if (function is None):
         return dot
      if (not function.instructionData):
         function.instructionData = function.disassembleFunction()
      headInstruction = function.instructionData
      #dot.node(function.offsetStart, function.name)
      while (headInstruction):
         if ("CALL" in headInstruction.opcode):
            offset = int(headInstruction.id) - (prime - int(headInstruction.imm))
            if (offset < 0 ):
               offset = int(headInstruction.id) + int(headInstruction.imm)
            if (str(offset) != function.offsetStart and (function.offsetStart, str(offset)) not in edgesDone):
               edgesDone.append((function.offsetStart, str(offset)))
               self.buildCallFlowGraph(dot, self.getFunctionAtOffset(str(offset)), edgesDone)
               dot.edge(function.offsetStart, str(offset))
         headInstruction = headInstruction.nextInstruction
      return dot

   def printCallFlowGraph(self):
      if (self.dot == None):
         dot = graphviz.Digraph('CALL FLOW GRAPH', comment='CALL FLOW GRAPH')
         for function in self.functions:
            dot.node(function.offsetStart, function.name)
         edgesDone = []
         for function in self.functions:
            self.dot = self.buildCallFlowGraph(dot, function, edgesDone)
      self.dot.render(directory='doctest-output', view=True)
      return self.dot

class InstructionData:
   def __init__(self, instructionData, id):
      self.id = id
      self.offDest = instructionData.get("off0") if instructionData.get("off0")[0] == '-' else '+' + instructionData.get("off0")
      self.offDest = self.offDest if int(self.offDest) != 0 else ""
      self.off1 = instructionData.get("off1") if instructionData.get("off1")[0] == '-' else '+' + instructionData.get("off1")
      self.off1 = self.off1 if int(self.off1) != 0 else ""
      self.off2 = instructionData.get("off2") if instructionData.get("off2")[0] == '-' else '+' + instructionData.get("off2")
      self.off2 = self.off2 if int(self.off2) != 0 else ""
      self.imm = instructionData.get("imm")
      self.dstRegister = instructionData.get("dst_register").split("Register.")[1]
      self.op0Register = instructionData.get("op0_register").split("Register.")[1]
      self.op1Addr = instructionData.get("op1_addr").split("Op1Addr.")[1]
      self.res = instructionData.get("res").split("Res.")[1]
      self.pcUpdate = instructionData.get("pc_update").split("PcUpdate.")[1]
      self.apUpdate = instructionData.get("ap_update").split("ApUpdate.")[1]
      self.fpUpdate = instructionData.get("fp_update").split("FpUpdate.")[1]
      self.opcode = instructionData.get("opcode").split("Opcode.")[1]
      self.nextInstruction = None

   def handleAssertEq(self):
      fPrint(f"{self.opcode}", end="")
      if ("OP1" in self.res):
         if ("IMM" in self.op1Addr):
               fPrint(f"[{self.dstRegister}{self.offDest}], {self.imm}")
         elif ("OP0" in self.op1Addr):
               fPrint(f"[{self.dstRegister}{self.offDest}], [[{self.op0Register}{self.off1}]{self.off2}]")
         else:
               fPrint(f"[{self.dstRegister}{self.offDest}], [{self.op1Addr}{self.off2}]") 
      else:
         op = operator[self.res]
         if ("IMM" not in self.op1Addr):
               fPrint(f"[{self.dstRegister}{self.offDest}], [{self.op0Register}{self.off1}] {op} [{self.op1Addr}{self.off2}]")  
         else:
               fPrint(f"[{self.dstRegister}{self.offDest}], [{self.op0Register}{self.off1}] {op} {self.imm}")
   
   def handleNop(self):
      if ("REGULAR" not in self.pcUpdate):
         ##TODO JNZ OFFSET ?!
         fPrint(f"{self.pcUpdate}", end="")
         fPrint(self.imm)
      else:
         fPrint(f"{self.opcode}")
      #newOffset = int(self.id) + int(self.imm)
      #fPrint(f"{newOffset}")

   def handleCall(self):
      fPrint(f"{self.opcode}", end="")
      offset = int(self.id) - (prime - int(self.imm))
      if (offset < 0):
         offset = int(self.id) + int(self.imm)
      fPrint(f"{offset}")
      #fPrint(f"{offset}=>{##need to get the function name}")

   def handleRet(self):
      fPrint(f"{self.opcode}")

class FunctionData:
   def __init__(self, offsetStart, offsetEnd, name, instructionList, args, ret, decorators, analyze=True) -> None:
      self.offsetStart = offsetStart
      self.offsetEnd = offsetEnd
      self.name = name
      self.instructionList = instructionList
      self.args = args if args != {} else None
      self.ret = ret if ret != {} else None
      self.decorators = decorators
      self.instructionData = None
      self.nextFunction = None
      self.entryPoint = False

   def disassembleFunction(self):
      instructionList = self.instructionList
      head = None
      previous = None
      instructionData = None
      for offset in instructionList:
         for bytecode in instructionList[offset]:
               instructionData = InstructionData(instructionList[offset][bytecode], offset)
         if (not head):
               head = instructionData
         if (previous):
               previous.nextInstruction = instructionData
         previous = instructionData
      self.instructionData = head
   
   def getPrototype(self):
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

   def printData(self):
      instructionData = self.instructionData
      prototype = self.getPrototype()
      print(f"\n\t\t{prototype}\n")
      while instructionData:
         fPrint(f"offset {instructionData.id}:", end="")
         if ("ASSERT_EQ" in instructionData.opcode):
               instructionData.handleAssertEq()
         
         elif ("NOP" in instructionData.opcode):
               instructionData.handleNop()
         
         elif ("CALL" in instructionData.opcode):
               instructionData.handleCall()

         elif ("RET" in instructionData.opcode):
               instructionData.handleRet()

         else:
               fPrint("--TODO--")

         if ("REGULAR" not in instructionData.apUpdate):
               op = list(filter(None, re.split(r'(\d+)', instructionData.apUpdate)))
               APopcode = op[0]
               APval = op[1] if (len(op) > 1) else instructionData.imm
               fPrint(f"offset {instructionData.id}:", end="")
               fPrint(f"{APopcode}", end="")
               fPrint(f"AP, {APval}")
         instructionData = instructionData.nextInstruction