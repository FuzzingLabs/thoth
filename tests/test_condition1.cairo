func main{}():
	[ap] = 50; ap++

	if [ap-1] == 50:
		[ap] = 25; ap++
		[ap] = 10; ap++
	else:
		[ap] = 2; ap++
	end
	[ap] = [ap-1]
	ret
end

{
   "Instruction 2": {
      "5198420613823168512": {
         "off0": "0",
         "off1": "-1",
         "off2": "1",
         "imm": "50",
         "dst_register": "Register.AP",
         "op0_register": "Register.FP",
         "op1_addr": "Op1Addr.IMM",
         "res": "Res.OP1",
         "pc_update": "PcUpdate.REGULAR",
         "ap_update": "ApUpdate.ADD1",
         "fp_update": "FpUpdate.REGULAR",
         "opcode": "Opcode.ASSERT_EQ"
      }
   },
   "Instruction 4": {
      "145944781866893311": {
         "off0": "0",
         "off1": "-1",
         "off2": "1",
         "imm": "3618502788666131213697322783095070105623107215331596699973092056135872020431",
         "dst_register": "Register.AP",
         "op0_register": "Register.AP",
         "op1_addr": "Op1Addr.IMM",
         "res": "Res.ADD",
         "pc_update": "PcUpdate.REGULAR",
         "ap_update": "ApUpdate.ADD1",
         "fp_update": "FpUpdate.REGULAR",
         "opcode": "Opcode.ASSERT_EQ"
      }
   },
   "Instruction 6": {
      "5189976364521848832": {
         "off0": "-1",
         "off1": "-1",
         "off2": "1",
         "imm": "8",
         "dst_register": "Register.AP",
         "op0_register": "Register.FP",
         "op1_addr": "Op1Addr.IMM",
         "res": "Res.UNCONSTRAINED",
         "pc_update": "PcUpdate.JNZ",
         "ap_update": "ApUpdate.REGULAR",
         "fp_update": "FpUpdate.REGULAR",
         "opcode": "Opcode.NOP"
      }
   },
   "Instruction 8": {
      "5189976364521848832": {
         "off0": "0",
         "off1": "-1",
         "off2": "1",
         "imm": "25",
         "dst_register": "Register.AP",
         "op0_register": "Register.FP",
         "op1_addr": "Op1Addr.IMM",
         "res": "Res.OP1",
         "pc_update": "PcUpdate.REGULAR",
         "ap_update": "ApUpdate.ADD1",
         "fp_update": "FpUpdate.REGULAR",
         "opcode": "Opcode.ASSERT_EQ"
      }
   },
   "Instruction 10": {
      "74168662805676031": {
         "off0": "0",
         "off1": "-1",
         "off2": "1",
         "imm": "10",
         "dst_register": "Register.AP",
         "op0_register": "Register.FP",
         "op1_addr": "Op1Addr.IMM",
         "res": "Res.OP1",
         "pc_update": "PcUpdate.REGULAR",
         "ap_update": "ApUpdate.ADD1",
         "fp_update": "FpUpdate.REGULAR",
         "opcode": "Opcode.ASSERT_EQ"
      }
   },
   "Instruction 12": {
      "5189976364521848832": {
         "off0": "-1",
         "off1": "-1",
         "off2": "1",
         "imm": "4",
         "dst_register": "Register.FP",
         "op0_register": "Register.FP",
         "op1_addr": "Op1Addr.IMM",
         "res": "Res.OP1",
         "pc_update": "PcUpdate.JUMP_REL",
         "ap_update": "ApUpdate.REGULAR",
         "fp_update": "FpUpdate.REGULAR",
         "opcode": "Opcode.NOP"
      }
   },
   "Instruction 14": {
      "4616893303349018624": {
         "off0": "0",
         "off1": "-1",
         "off2": "1",
         "imm": "2",
         "dst_register": "Register.AP",
         "op0_register": "Register.FP",
         "op1_addr": "Op1Addr.IMM",
         "res": "Res.OP1",
         "pc_update": "PcUpdate.REGULAR",
         "ap_update": "ApUpdate.ADD1",
         "fp_update": "FpUpdate.REGULAR",
         "opcode": "Opcode.ASSERT_EQ"
      }
   },
   "Instruction 15": {
      "2345108766317314046": {
         "off0": "0",
         "off1": "-1",
         "off2": "-1",
         "imm": "None",
         "dst_register": "Register.AP",
         "op0_register": "Register.FP",
         "op1_addr": "Op1Addr.AP",
         "res": "Res.OP1",
         "pc_update": "PcUpdate.REGULAR",
         "ap_update": "ApUpdate.REGULAR",
         "fp_update": "FpUpdate.REGULAR",
         "opcode": "Opcode.ASSERT_EQ"
      }
   }
}