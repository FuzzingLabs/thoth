from graphviz import Digraph
from typing import List, Tuple

from sierra.utils import colors

# CFG Edges types
EDGE_UNCONDITIONAL = "unconditional"
EDGE_CONDITIONAL_TRUE = "conditional_true"
EDGE_CONDITIONAL_FALSE = "conditional_false"
EDGE_FALLTHROUGH = "fallthrough"


class Edge:
    """
    Sierra Control Flow Graph Edge class
    """

    def __init__(self, source: int, destination: int, type: str = EDGE_UNCONDITIONAL) -> None:
        self.source = source
        self.destination = destination
        self.type = type


class SierraType:
    """
    Sierra Type class
    """

    def __init__(self, id: str) -> None:
        self.id = id


class SierraStatement:
    """
    Sierra Statement class
    """

    offset = 0

    def __init__(self, raw_statement: str) -> None:
        self.raw_statement = raw_statement
        self.offset = SierraStatement.offset
        SierraStatement.offset += 1


class SierraVariable:
    """
    Sierra Variable class
    """

    def __init__(self, name: int, type: SierraType = None) -> None:
        self.name = name
        self.representation_name = "var_%s" % self.name
        self.type = type


class SierraFunction:
    """
    Sierra Function class
    """

    def __init__(
        self,
        id: str,
        start_offset: int,
        parameters: List[SierraVariable],
        return_values_types: List[SierraType],
    ) -> None:
        self.id = id
        # Function delimitation
        self.start_offset = start_offset
        self.end_offset = None
        # Prototype
        self.parameters = parameters
        self.return_values_types = return_values_types
        # Statements
        self.statements: List[SierraStatement] = []
        # CFG
        self.cfg = SierraControlFlowGraph(self)

    @property
    def prototype(self) -> str:
        """
        Return the formatted function prototype
        func <name> (<arguments, ...>) -> (<return values, ...>)
        """

        # Prototype elements
        function_name = self.id
        function_arguments = ", ".join(
            ["%s: %s" % (a.representation_name, a.type[0].id) for a in self.parameters]
        )
        function_return_values = "(" + ", ".join([t[0].id for t in self.return_values_types]) + ")"

        # Format the prototype
        prototype = "func %s (%s) -> %s" % (
            function_name,
            function_arguments,
            function_return_values,
        )
        return prototype


class SierraBasicBlock:
    """
    Sierra Control-Flow Graph basic block class
    """

    def __init__(self, start_statement: SierraStatement) -> None:
        # Basic block delimitations
        self.start_statement = start_statement
        self.start_offset = start_statement.offset
        self.end_offset = None
        # Name
        self.name = SierraBasicBlock._name(self.start_offset)
        # Instructions
        self.statements: List[SierraStatement] = []
        # Edges
        self.edges: List[Edge] = []

    @staticmethod
    def _name(statement_offset: int) -> str:
        return "bb_%s" % str(statement_offset)


class SierraLibFunc:
    """
    Sierra LibFunc class
    """

    def __init__(self, id: str, name: str) -> None:
        self.id = id
        self.name = name


class SierraConditionalBranch(SierraStatement):
    """
    Sierra conditional branch class
    """

    def __init__(
        self,
        function: SierraLibFunc,
        parameters: List[SierraVariable],
        edge_1_offset: int,
        edge_2_offset: int = None,
        fallthrough: bool = False,
        *args,
        **kwargs,
    ) -> None:
        super(SierraConditionalBranch, self).__init__(*args, **kwargs)
        # Function prototype
        self.function = function
        self.parameters = parameters
        # Edges offsets
        self.edge_1_offset = edge_1_offset
        self.edge_2_offset = edge_2_offset
        # Fallthrough conditional branch
        self.fallthrough = fallthrough
        if fallthrough:
            self.edge_2_offset = self.offset


class SierraControlFlowGraph:
    """
    Sierra Control-Flow graph class
    """

    def __init__(self, function: SierraFunction) -> None:
        """
        Initialize the Sierra Control-Flow graph
        """
        self.function = function
        self.basic_blocks = []
        self.dot = None

    def _get_basic_blocks_delimitations(self) -> Tuple[List[int], List[int]]:
        """
        Generate the lists of basic blocks starts and ends offsets
        """
        basic_blocks_starts = [self.function.start_offset]
        basic_blocks_ends = []

        for statement in self.function.statements:
            # Return statement
            if isinstance(statement, SierraReturn):
                basic_blocks_ends.append(statement.offset)
            # Conditional branch
            elif isinstance(statement, SierraConditionalBranch):
                basic_blocks_starts.append(statement.offset + 1)
                basic_blocks_starts.append(statement.edge_1_offset)

                basic_blocks_ends.append(statement.offset)

        return (basic_blocks_starts, basic_blocks_ends)

    def _generate_basic_blocks(self) -> None:
        """
        Generate the CFG basic blocks
        """
        # Basic blocks delimitations
        basic_blocks_starts, basic_blocks_ends = self._get_basic_blocks_delimitations()

        # Create basic blocks
        new_basic_block = True
        current_basic_block = SierraBasicBlock(self.function.statements[0])
        for i in range(len(self.function.statements)):
            statement = self.function.statements[i]

            # If the instruction is at the beginning of a basic block
            if statement.offset in basic_blocks_starts:
                new_basic_block = True
                self.basic_blocks.append(current_basic_block)

            # Create a new basic block
            if new_basic_block:
                current_basic_block = SierraBasicBlock(statement)
                new_basic_block = False

            # Add instruction to the current block
            current_basic_block.statements.append(statement)

            # End of a basic block
            if statement.offset in basic_blocks_ends:
                new_basic_block = True

            if isinstance(statement, SierraConditionalBranch):
                # Conditional branch with 2 edges (JNZ)
                if statement.edge_2_offset is not None:

                    current_basic_block.edges.append(
                        Edge(
                            source=statement.offset,
                            destination=statement.edge_1_offset,
                            type=EDGE_CONDITIONAL_TRUE,
                        )
                    )
                    current_basic_block.edges.append(
                        Edge(
                            source=statement.offset,
                            destination=statement.edge_2_offset + 1,
                            type=EDGE_CONDITIONAL_FALSE,
                        )
                    )
                # Conditional jump with 1 edge (JUMP)
                else:
                    current_basic_block.edges.append(
                        Edge(
                            source=statement.offset,
                            destination=statement.edge_1_offset,
                            type=EDGE_UNCONDITIONAL,
                        )
                    )

            elif i < (len(self.function.statements) - 1):
                if (
                    self.function.statements[i + 1].offset
                ) in basic_blocks_starts and not isinstance(statement, SierraReturn):
                    current_basic_block.edges.append(
                        Edge(
                            source=statement.offset,
                            destination=statement.offset + 1,
                            type=EDGE_FALLTHROUGH,
                        )
                    )

        self.basic_blocks.append(current_basic_block)

    def _generate_cfg(self) -> None:
        """
        Generate the CFG dot graph
        """
        # Create the function cluster
        cluster_name = "cluster_%s" % self.function.id
        self.dot = Digraph(cluster_name, comment=cluster_name)
        self.dot.attr(label=cluster_name)

        # Create the basic blocks labels
        basic_blocks_offsets = [b.start_offset for b in self.basic_blocks]
        for block in self.basic_blocks:
            # Create all the basicblock nodes
            shape = "square"
            label_instruction = ""
            for statement in block.statements:
                label_instruction += str(statement.offset) + " : " + statement.raw_statement + "\\l"
            self.dot.node(block.name, label=label_instruction, shape=shape)

            # Iterate over edges_offset and create the edges
            for edge in block.edges:
                offset = edge.destination
                # If branch
                if edge.type == EDGE_CONDITIONAL_TRUE:
                    color = "green"
                # Else branch
                elif edge.type == EDGE_CONDITIONAL_FALSE:
                    color = "red"
                # Jump
                elif edge.type == EDGE_UNCONDITIONAL:
                    color = "blue"
                # Fallthrough
                else:
                    color = "black"

                if offset in basic_blocks_offsets:
                    self.dot.edge(
                        SierraBasicBlock._name(block.start_offset),
                        SierraBasicBlock._name(offset),
                        color=color,
                    )

    def _get_cfg(self) -> str:
        """
        Return CFG Dot graph
        """
        return self.dot


class SierraVariableAssignation(SierraStatement):
    """
    Sierra Variable assignation class
    """

    def __init__(
        self,
        function: SierraLibFunc,
        function_arguments: List[SierraVariable],
        assigned_variables: List[SierraVariable],
        *args,
        **kwargs,
    ) -> None:
        super(SierraVariableAssignation, self).__init__(*args, **kwargs)
        self.function = function
        self.libfunc_arguments = function_arguments
        self.assigned_variables = assigned_variables

    @property
    def formatted_statement(self):
        function_arguments = ", ".join([v.representation_name for v in self.libfunc_arguments])
        function_call = "%s%s%s(%s)" % (
            colors.CYAN,
            self.function.id,
            colors.ENDC,
            function_arguments,
        )

        # Variables assigned with a function call
        if self.assigned_variables:
            assigned_variables = ", ".join([v.representation_name for v in self.assigned_variables])
            formatted_statement = "%s = %s" % (assigned_variables, function_call)
        # Function call without assignation
        else:
            formatted_statement = "%s" % function_call
        return formatted_statement


class SierraReturn(SierraStatement):
    """
    Sierra return class
    """

    def __init__(self, variables: List[SierraVariable], *args, **kwargs) -> None:
        super(SierraReturn, self).__init__(*args, **kwargs)
        self.variables = variables

    @property
    def formatted_statement(self):
        returned_variables = ", ".join([v.representation_name for v in self.variables])
        formatted_statement = "%sreturn%s (%s)" % (colors.RED, colors.ENDC, returned_variables)
        return formatted_statement
