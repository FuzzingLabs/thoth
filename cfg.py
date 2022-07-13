import re
class BasicBlock:
    """
    BasicBlock Class
    """
    def __init__(self, start_instr):
        self.start_instr = start_instr
        self.start_offset = self.start_instr.id
        self.name = format_bb_name(self.start_instr.id)

        self.end_offset = None
        self.end_instr = None
        self.instructions = []
        self.edges_offset = []

    def set_instructions(self, instrs):
        self.instructions = instrs

    def print(self):
        # TODO - replace by instr code
        return format_bb_name(self.start_offset)

def format_bb_name(instr_offset):
    return f'bb_{instr_offset}'

class CFG:
    """
    CFG class

    Create a Control Flow Graph per Function
    """
    def __init__(self, instructions, dot):
        self.dot = dot
        self.basicblocks = []

        self._generate_basicblocks(instructions)
        self.generate_cfg()


    def set_basicblocks(self, bbs):
        self.basicblocks = bbs


    def _generate_basicblocks(self, instructions):

        list_bb = list()
        last_func_instr = instructions[-1]
        new_bb = True
        current_bb = None


        for instr in instructions:

            # create a basicblock
            if new_bb:
                current_bb = BasicBlock(instr)
                new_bb = False
            
            current_bb.instructions.append(instr)

            # Return - Stop the execution
            if ("RET" in instr.opcode):
                current_bb.end_instr = instr
                current_bb.end_offset = instr.id
                list_bb.append(current_bb)
                new_bb = True
                
            # Jump to instr offset + instr.imm
            elif ("JUMP_REL" in instr.pcUpdate):
                if ("CALL" not in instr.opcode):
                    current_bb.end_instr = instr
                    current_bb.end_offset = instr.id
                    list_bb.append(current_bb)
                    current_bb.edges_offset.append(str(int(instr.id) + int(instr.imm)))
                    new_bb = True
                    
            # Jump to instr offset + instr.imm
            elif ("JUMP" in instr.pcUpdate):
                current_bb.end_instr = instr
                current_bb.end_offset = instr.id
                current_bb.edges_offset.append(str(int(instr.id) + int(instr.imm)))
                list_bb.append(current_bb)
                new_bb = True
                
            # Jump to instr offset + instr.imm
            # or instr offset + 2
            elif ("JNZ" in instr.pcUpdate):
                current_bb.end_instr = instr
                current_bb.end_offset = instr.id
                current_bb.edges_offset.append(str(int(instr.id) + int(instr.imm)))
                current_bb.edges_offset.append(str(int(instr.id) + int(2)))
                list_bb.append(current_bb)
                new_bb = True
                
            else:
                # Should never happen
                # all function finish by RET
                if instr is last_func_instr:
                    raise AssertionError


        # TODO - handle case 
        # jmp rel in the middle other basicblock
        # ex: tests/json_files/cairo_jmp.json              

        current_bb.end_instr = instr
        current_bb.end_offset = instr.id
        self.set_basicblocks(list_bb)

    def print_bb(self):
        print()
        for bb in self.basicblocks:
            print(f'-- BB {bb.name, len(bb.instructions)} {bb.edges_offset} --')
            for instr in bb.instructions:
                print(instr.print())
            print()

    def generate_cfg(self):
        """
        Create the basicblock nodes and the edges
        """        
        # get all bb offset
        bb_offsets = [bb.start_offset for bb in self.basicblocks]

        # build the edges btw basicblocks
        for bb in self.basicblocks:

            # Create all the basicblock nodes
            shape = 'square'
            label_instruction = ""
            for instr in bb.instructions:
                label_instruction += re.sub('\s+', ' ', instr.print().replace("\n", "\\n"))
            self.dot.node(bb.name,
                          label=label_instruction,
                          shape=shape)

            # iterate over edges_offset
            for offset in bb.edges_offset:

                # we check that we are not creating an edge 
                # to an offset that is not a bb start offset
                # TODO - support weird `jmp rel 7` type
                if offset in bb_offsets:
                    self.dot.edge(format_bb_name(bb.start_offset), format_bb_name(offset))

    def print(self, view=True):
        self.print_bb()
        return self.dot
