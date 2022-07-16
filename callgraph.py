from graphviz import Digraph
from utils import field_element_repr, PRIME, CALLGRAPH_ENTRYPOINT, CALLGRAPH_IMPORT, CALLGRAPH_INDIRECT_CALL, CALLGRAPH_NODE_ATTR, CALLGRAPH_GRAPH_ATTR, CALLGRAPH_EDGE_ATTR

class CallFlowGraph:
    """
    CallFlowGraph class

    Create a call flow graph for the contract
    """
    def __init__(self, functions):
        self.dot = None
        self._generate_call_flow_graph(functions)


    def _call_flow_graph_generate_nodes(self, functions):
        """
        Create all the function nodes
        """
        # TODO - issue #44

        for function in functions:

            # Default values
            shape = 'oval'
            color = ''
            style = 'solid'

            # This function is an entrypoint
            if function.entry_point:
                shape=CALLGRAPH_ENTRYPOINT['shape']
                style=CALLGRAPH_ENTRYPOINT['style']
                color=CALLGRAPH_ENTRYPOINT['color']

            # This function is an import
            if function.is_import:
                style=CALLGRAPH_IMPORT['style']
                color=CALLGRAPH_IMPORT['color']

            # Search if this function is doing indirect_calls
            if any(inst.is_call_indirect() for inst in function.instructions):
                style=CALLGRAPH_INDIRECT_CALL['style']

            # Create the function node
            self.dot.node(function.offset_start,
                                 label=function.name,
                                 shape=shape,
                                 style=style,
                                 color=color)


    def _generate_call_flow_graph(self, functions):
        """
        Create all the function Node for the CallFlowGraph and call _generate_call_flow_graph_edges to build the edges
        """
        # Create the directed graph
        self.dot = Digraph('Call flow graph',
                           comment='Call flow graph',
                           node_attr=CALLGRAPH_NODE_ATTR,
                           graph_attr=CALLGRAPH_GRAPH_ATTR,
                           edge_attr=CALLGRAPH_EDGE_ATTR)

        # First, we create the nodes
        self._call_flow_graph_generate_nodes(functions)

        edges = []
        # Build the edges btw functions (nodes)
        for function in functions:
            for inst in function.instructions:
                if inst.is_call_direct():
                    # direct CALL to a fonction
                    if inst.call_xref_func_name is not None:
                        offset = int(inst.id) - int(field_element_repr(int(inst.imm), PRIME))
                        if offset < 0:
                            offset = int(inst.id) + int(inst.imm)
                        edges.append((function.offset_start, offset))
                    else:
                        # relative CALL
                        pass
                elif inst.is_call_indirect():
                    # indirect call
                    # we can't create any edges without evaluating the stack
                    pass

        # Create the edges inside the dot
        while len(edges) > 0:
            # Multiple edges are the same
            if edges.count(edges[0]) > 1:
                self.dot.edge(str(edges[0][0]), str(edges[0][1]), label=str(edges.count(edges[0])))
            # Unique edge
            else:
                self.dot.edge(str(edges[0][0]), str(edges[0][1]))
            edges = list(filter(lambda x: x != edges[0], edges))


    def print(self, view=True):
        """
        Render the CallFlowGraph
        """
        self.dot.render(directory='output-callgraph', view=view)
        return self.dot
