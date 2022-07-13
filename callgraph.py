from graphviz import Digraph
from utils import PRIME

class CallGraph:
    """
    CallGraph class

    Create a call flow graph for the all contract
    """
    def __init__(self, functions):
        self.dot = None
        self._generate_call_flow_graph(functions)


    def _call_flow_graph_generate_nodes(self, functions):
            """
            Create all the function nodes
            """

            # TODO - add import info
            for function in functions:

                # default shape
                shape = 'oval'

                # This function is an entrypoint
                if function.entry_point:
                    shape = 'doubleoctagon'

                self.dot.node(function.offset_start,
                                     label=function.name,
                                     shape=shape)
        

    def _generate_call_flow_graph(self, functions):
        """
        Create all the function Node for the CallFlowGraph and call _generate_call_flow_graph_edges to build the edges
        """
        self.dot = Digraph('CALL FLOW GRAPH', comment='CALL FLOW GRAPH')
        
        # First, we create the nodes
        self._call_flow_graph_generate_nodes(functions)

        edgesDone = []
        # build the edges btw function (nodes)
        for function in functions:
            for instr in function.instructions:
                if ("CALL" in instr.opcode):
                    offset = int(instr.id) - (PRIME - int(instr.imm))
                    if (offset < 0):
                        offset = int(instr.id) + int(instr.imm)
                    if (str(offset) != function.offset_start and (function.offset_start, str(offset)) not in edgesDone):
                        edgesDone.append((function.offset_start, str(offset)))
                        self.dot.edge(function.offset_start, str(offset))


    def print(self, view=True):
        self.dot.render(directory='doctest-output', view=view)
        return self.dot
