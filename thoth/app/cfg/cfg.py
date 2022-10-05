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
        self.is_phi_node = None
        self.variables: List = []

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
        self.find_phi_nodes()

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

        # List of block beginnings
        basic_blocks_starts = [0]
        # List of block ends
        basic_blocks_end = []

        for instruction in instructions:
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
                basic_blocks_end.append(instruction.id)

            # Jump to instr offset + instr.imm
            elif ("JUMP" in instruction.pcUpdate) or (
                "JUMP_REL" in instruction.pcUpdate and "CALL" not in instruction.opcode
            ):
                basic_blocks_starts.append((str(int(instruction.id) + int(instruction.imm))))

            # Jump to instr offset + instr.imm
            # or instr offset + 2
            elif "JNZ" in instruction.pcUpdate:
                basic_blocks_starts.append(str(int(instruction.id) + int(instruction.imm)))
                basic_blocks_starts.append(str(int(instruction.id) + int(2)))

            else:
                if instruction is last_function_instruction:
                    raise AssertionError

        basic_blocks_starts = [int(start) for start in basic_blocks_starts]
        basic_blocks_end = [int(end) for end in basic_blocks_end]

        # Init the first basic block
        current_basic_block = BasicBlock(instructions[0])

        phi_node_block = None
        new_basic_block = True
        for i in range(1, len(instructions)):
            instruction = instructions[i]

            # If the instruction is at the beginning of a basic block
            if int(instruction.id) in basic_blocks_starts:
                new_basic_block = True
                list_basic_block.append(current_basic_block)
            # Create a new Basic Block
            if new_basic_block:
                current_basic_block = BasicBlock(instruction)
                new_basic_block = False

            # Add instruction to the current block
            current_basic_block.instructions.append(instruction)

            imm = int(instruction.imm) if instruction.imm != "None" else 0
            # Create edges
            if instruction.is_return():
                pass
            # JUMP
            elif ("JUMP" in instruction.pcUpdate) and (
                "JUMP_REL" in instruction.pcUpdate and "CALL" not in instruction.opcode
            ):
                current_basic_block.edges_offset.append((str(int(instruction.id) + imm)))
                phi_node_block = str(int(instruction.id) + imm)
            # JNZ
            elif "JNZ" in instruction.pcUpdate:
                current_basic_block.edges_offset.append(str(int(instruction.id) + imm))
                current_basic_block.edges_offset.append(str(int(instruction.id) + int(2)))
            # End of block
            elif i < (len(instructions) - 1):
                if int(instructions[i + 1].id) in basic_blocks_starts:
                    current_basic_block.edges_offset.append(phi_node_block)
            new_basic_block = False

        # Append the last basic block to the list
        list_basic_block.append(current_basic_block)
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

    def parents(self, basic_block: BasicBlock) -> List[BasicBlock]:
        """
        Return a list of the parents of a basic_block
        """
        parents = []

        start_offset = int(basic_block.start_offset)
        end_offset = int(basic_block.end_offset)
        for basic_block in self.basicblocks:
            edges_offset = [int(offset) for offset in basic_block.edges_offset]
            for offset in edges_offset:
                if start_offset <= offset <= end_offset:
                    parents.append(basic_block)
        return parents

    def find_phi_nodes(self) -> None:
        """
        Find the basic blocks that are phi nodes
        """
        for i in range(len(self.basicblocks)):
            block = self.basicblocks[i]
            block.is_phi_node = False
            if i > 0:
                if len(block.edges_offset) == 2:
                    block.is_phi_node = True
