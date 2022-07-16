from cProfile import label
from graphviz import Digraph
from utils import field_element_repr, PRIME, CALLGRAPH_ENTRYPOINT, CALLGRAPH_IMPORT, CALLGRAPH_INDIRECT_CALL, CALLGRAPH_NODE_ATTR, CALLGRAPH_GRAPH_ATTR, CALLGRAPH_EDGE_ATTR

class CallFlowGraph:
    """
    CallFlowGraph class

    Create a call flow graph for the all contract
    """
    def __init__(self, functions):
        self.dot = None

        self._generate_call_flow_graph(functions)


    def _call_flow_graph_generate_nodes(self, functions):
            """
            Create all the function nodes
            """

            # TODO - add decorator info (color shape)

            for function in functions:

                # default values
                shape = 'oval'
                color = ''
                style = 'solid'

                # This function is an entrypoint
                if function.entry_point:
                    shape=CALLGRAPH_ENTRYPOINT['shape']
                    style=CALLGRAPH_ENTRYPOINT['style']
                    color=CALLGRAPH_ENTRYPOINT['color']

                # this func is an import
                if function.is_import:
                    style=CALLGRAPH_IMPORT['style']
                    color=CALLGRAPH_IMPORT['color']

                # Search if this function is doing indirect_calls
                is_doing_indirect_call = any(inst.is_call_indirect() for inst in function.instructions)

                if is_doing_indirect_call:
                    style=CALLGRAPH_INDIRECT_CALL['style']

                self.dot.node(function.offset_start,
                                     label=function.name,
                                     shape=shape,
                                     style=style,
                                     color=color)
        

    def _generate_call_flow_graph(self, functions):
        """
        Create all the function Node for the CallFlowGraph and call _generate_call_flow_graph_edges to build the edges
        """
        self.dot = Digraph('Call flow graph',
                           comment='Call flow graph',
                           node_attr=CALLGRAPH_NODE_ATTR,
                           graph_attr=CALLGRAPH_GRAPH_ATTR,
                           edge_attr=CALLGRAPH_EDGE_ATTR)

        # First, we create the nodes
        self._call_flow_graph_generate_nodes(functions)

        edges = []
        
        # build the edges btw function (nodes)
        for function in functions:
            for inst in function.instructions:
                if inst.is_call_direct():
                    # direct CALL to a fonction
                    if inst.call_xref_func_name != None:
                        offset = int(inst.id) - int(field_element_repr(int(inst.imm), PRIME))
                        if (offset < 0):
                            offset = int(inst.id) + int(inst.imm)
                    else:
                        # relative CALL
                        offset = int(inst.id) + int(field_element_repr(int(inst.imm), PRIME))
                    edges.append((function.offset_start, offset))
                elif inst.is_call_indirect():
                    # indirect call
                    # we can't create any edges without evaluating the stack
                    pass

        while (len(edges) > 0):
            if (edges.count(edges[0]) > 1):
                self.dot.edge(str(edges[0][0]), str(edges[0][1]), label=str(edges.count(edges[0])))
            else:
                self.dot.edge(str(edges[0][0]), str(edges[0][1]))
            edges = list(filter(lambda x: x != edges[0], edges))


    def print(self, view=True):
        self.dot.render(directory='output-callgraph', view=view)
        return self.dot
