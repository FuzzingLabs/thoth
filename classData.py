import imp
import graphviz
import re
from utils import *
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
         fPrint(f"{self.pcUpdate}", end="")
      else:
         fPrint(f"{self.opcode}", end="")
      #newOffset = int(self.id) + int(self.imm)
      #fPrint(f"{newOffset}")

   def handleCall(self):
      fPrint(f"{self.opcode}", end="")
      offset = int(self.id) - (prime - int(self.imm))
      fPrint(f"{offset}")
      #fPrint(f"{offset}=>{##need to get the function name}")

   def handleRet(self):
      fPrint(f"{self.opcode}")
      
class FunctionDict:
   def __init__(self):
      self.functions = {}
   
   def append(self, functionData):
      self.functions[functionData.offsetStart] = functionData
   
   def getFunctionAtOffset(self, offset):
      return (self.functions.get(offset))

class FunctionData:
   def __init__(self, offsetStart, offsetEnd, name, instructionList, analyze=True) -> None:
      self.offsetStart = offsetStart
      self.offsetEnd = offsetEnd
      self.name = name
      self.instructionList = instructionList
      self.instructionData = None
      self.nextFunction = None
      self.dictFunctions = None

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

   def printData(self):
      instructionData = self.instructionData
      print(f"\n\t\tFUNCTION : {self.name}\n")
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
   
   def cfgFunction(self, dot):
      if (not self.instructionData):
         self.instructionData = self.disassembleFunction()
      headInstruction = self.instructionData
      dot.node(self.offsetStart, self.name)
      while (headInstruction):
         if ("CALL" in headInstruction.opcode):
            offset = int(headInstruction.id) - (prime - int(headInstruction.imm))
            if (str(offset) != self.offsetStart):
               self.dictFunctions.getFunctionAtOffset(str(offset)).cfgFunction(dot)
            dot.edge(self.offsetStart, str(offset))
         headInstruction = headInstruction.nextInstruction
      