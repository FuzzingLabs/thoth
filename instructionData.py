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