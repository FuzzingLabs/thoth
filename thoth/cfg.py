#!/usr/bin/env python3

import re
from graphviz import Digraph


class BasicBlock:
    """Basic Block class object.
    """

    def __init__(self, start_instr):
        """Create the basic block object from the given instruction.

        Args:
            start_instr (Instruction): The given instruction.
        """
        self.start_instr = start_instr
        self.start_offset = self.start_instr.id
        self.name = format_bb_name(self.start_instr.id)

        self.end_offset = None
        self.end_instr = None
        self.instructions = []
        self.edges_offset = []

    def set_instructions(self, instrs):
        """Set the instruction list of the basic block.

        Args:
            instrs (Instruction List): The list containing all the instructions.
        """
        self.instructions = instrs

    def print(self):
        # TODO - replace by instr code
        return format_bb_name(self.start_offset)


def format_bb_name(instr_offset):
    return f"bb_{instr_offset}"


class CFG:
    """
    CFG class

    Create a Control Flow Graph per Function
    """

    def __init__(self, func_name, instructions):
        self.dot = None
        self.func_name = func_name
        self.basicblocks = []
        self.name = f"CFG {self.func_name}"

        self._generate_basicblocks(instructions)
        self.generate_cfg()

    def set_basicblocks(self, bbs):
        """
        Setter for the list of BasicBlock
        """
        self.basicblocks = bbs

    def _generate_basicblocks(self, instructions):
        """
        Generate the internal list of BasicBlock
        """
        list_bb = []
        last_func_instr = instructions[-1]
        new_bb = True
        current_bb = None

        for instr in instructions:

            # Create a basicblock
            if new_bb:
                current_bb = BasicBlock(instr)
                new_bb = False

            current_bb.instructions.append(instr)

            # Direct CALL
            if instr.is_call_direct():
                # CALL direct to function
                pass
                # TODO - relative CALL to label
                pass

            # Indirect CALL
            elif instr.is_call_indirect():
                # Not interesting for the CFG
                pass

            # Return - Stop the execution
            elif instr.is_return():
                current_bb.end_instr = instr
                current_bb.end_offset = instr.id
                list_bb.append(current_bb)
                new_bb = True

            # Jump to instr offset + instr.imm
            elif ("JUMP" in instr.pcUpdate) or ("JUMP_REL" in instr.pcUpdate and "CALL" not in instr.opcode):
                current_bb.end_instr = instr
                current_bb.end_offset = instr.id
                current_bb.edges_offset.append(str(int(instr.id) + int(instr.imm)))
                list_bb.append(current_bb)
                new_bb = True

            # Jump to instr offset + instr.imm
            # or instr offset + 2
            elif "JNZ" in instr.pcUpdate:
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

        # TODO - how to handle if we have `jmp rel` to the middle of other basicblock
        # ex: tests/json_files/cairo_jmp.json

        self.set_basicblocks(list_bb)

    def print_bb(self):
        """
        Print the list of basic blocks in textual form
        """
        # TODO - issue #45
        print()
        for block in self.basicblocks:
            print(f"-- BB {block.name, len(block.instructions)} {block.edges_offset} --")
            for instr in block.instructions:
                print(instr.print())
            print()

    def generate_cfg(self):
        """
        Create the basicblock nodes and the edges
        """
        # Create the directed graph
        cluster_name = "cluster_" + self.name
        self.dot = Digraph(cluster_name, comment=self.name)
        self.dot.attr(label=self.name)

        # Find all the basicblocks offsets
        bb_offsets = [b.start_offset for b in self.basicblocks]

        # Build the edges btw basicblocks
        for block in self.basicblocks:

            # Create all the basicblock nodes
            shape = "square"
            label_instruction = ""
            for instr in block.instructions:
                label_instruction += re.sub("\s+", " ", instr.print().replace("\n", "\\l"))
            self.dot.node(block.name, label=label_instruction + "\\l", shape=shape)

            # Iterate over edges_offset
            for offset in block.edges_offset:
                color = "green"
                if offset is block.edges_offset[-1]:
                    color = "red"

                # We check that we are not creating an edge
                # to an offset that is not a block start offset
                # TODO - issue #43
                if offset in bb_offsets:
                    self.dot.edge(
                        format_bb_name(block.start_offset),
                        format_bb_name(offset),
                        color=color,
                    )

    def print(self, view=True):
        """
        Render the CFG in textual form
        """
        # TODO - issue #45
        self.print_bb()
        return self.dot
