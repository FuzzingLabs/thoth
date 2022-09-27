import re
from graphviz import Digraph
from typing import List
from thoth.app.disassembler.instruction import Instruction


class BasicBlock:
    """Basic Block class object."""

    def __init__(self, start_instruction: Instruction) -> None:
        """Create the basic block object from the given instruction.
        Args:
            start_instr (Instruction): The given instruction.
        """
        self.start_instruction = start_instruction
        self.start_offset = self.start_instruction.id
        self.name = BasicBlock.format_bb_name(self.start_instruction.id)

        self.end_offset = None
        self.end_instruction = None
        self.instructions: List[Instruction] = []
        self.edges_offset: List[Instruction] = []

    @staticmethod
    def format_bb_name(instruction_offset: int) -> str:
        return f"bb_{instruction_offset}"

    def set_instructions(self, instructions: List[Instruction]) -> None:
        """Set the instruction list of the basic block.
        Args:
            instrs (Instruction List): The list containing all the instructions.
        """
        self.instructions = instructions

    def print(self) -> str:
        # TODO - replace by instr code
        return BasicBlock.format_bb_name(self.start_offset)


class CFG:
    """
    CFG class

    Create a Control Flow Graph per Function
    """

    def __init__(self, function_name: str, instructions: List[Instruction]) -> None:
        """Create the CFG object
        Args:
            func_name (String): The name of the function
            instructions (List): List of instructions
        """
        self.dot = None
        self.function_name = function_name
        self.basicblocks: List[BasicBlock] = []
        self.name = f"CFG {self.function_name}"

        self._generate_basicblocks(instructions)
        self.generate_cfg()

    def set_basicblocks(self, basic_blocks: List[BasicBlock]) -> None:
        """Set the list of basicblocks
        Args:
            basic_blocks (List): The basicblocks list
        """
        self.basicblocks = basic_blocks

    def _generate_basicblocks(self, instructions: List[Instruction]):
        """Generate the internal list of BasicBlock


        Args:
            instructions (List): List of instructions

        Raises:
            AssertionError: Should never happen, all function finish by RET
        """
        list_basic_block: List[BasicBlock] = []
        last_function_instruction = instructions[-1]
        new_basic_block = True
        current_bb = None

        for instruction in instructions:

            # Create a basicblock
            if new_basic_block:
                current_bb = BasicBlock(instruction)
                new_basic_block = False

            current_bb.instructions.append(instruction)

            # Direct CALL
            if instruction.is_call_direct():
                # CALL direct to function
                pass
                # TODO - relative CALL to label
                pass

            # Indirect CALL
            elif instruction.is_call_indirect():
                # Not interesting for the CFG
                pass

            # Return - Stop the execution
            elif instruction.is_return():
                current_bb.end_instr = instruction
                current_bb.end_offset = instruction.id
                list_basic_block.append(current_bb)
                new_basic_block = True

            # Jump to instr offset + instr.imm
            elif ("JUMP" in instruction.pcUpdate) or (
                "JUMP_REL" in instruction.pcUpdate and "CALL" not in instruction.opcode
            ):
                current_bb.end_instr = instruction
                current_bb.end_offset = instruction.id
                current_bb.edges_offset.append(str(int(instruction.id) + int(instruction.imm)))
                list_basic_block.append(current_bb)
                new_basic_block = True

            # Jump to instr offset + instr.imm
            # or instr offset + 2
            elif "JNZ" in instruction.pcUpdate:
                current_bb.instruction = instruction
                current_bb.end_offset = instruction.id
                current_bb.edges_offset.append(str(int(instruction.id) + int(instruction.imm)))
                current_bb.edges_offset.append(str(int(instruction.id) + int(2)))
                list_basic_block.append(current_bb)
                new_basic_block = True

            else:
                if instruction is last_function_instruction:
                    raise AssertionError

        # TODO - how to handle if we have `jmp rel` to the middle of other basicblock
        # ex: tests/json_files/cairo_jmp.json

        self.set_basicblocks(list_basic_block)

    def print_bb(self) -> None:
        """Print the list of basic blocks in textual form"""
        # TODO - issue #45
        print()
        for block in self.basicblocks:
            print(f"-- BB {block.name, len(block.instructions)} {block.edges_offset} --")
            for instruction in block.instructions:
                print(instruction.print())
            print()

    def generate_cfg(self) -> None:
        """Create the basicblock nodes and the edges"""
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
                        BasicBlock.format_bb_name(block.start_offset),
                        BasicBlock.format_bb_name(offset),
                        color=color,
                    )

    def print(self) -> Digraph:
        """Print the dot

        Args:
            view (bool, optional): Set if the disassembler should open the output file or not. Defaults to True.

        Returns:
            Dot: the output Dot
        """
        self.print_bb()
        return self.dot
