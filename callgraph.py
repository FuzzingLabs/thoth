from cProfile import label
from graphviz import Digraph
import matplotlib.pyplot as plt
import networkx as nx
from utils import *

class CallFlowGraph:
    """
    CallFlowGraph class

    Create a call flow graph for the all contract
    """
    def __init__(self, functions):
        self.dot = None
        self.graph = None
        self._generate_call_flow_graph(functions)


    def _call_flow_graph_generate_nodes(self, functions):
        """
        Create all the function nodes
        """

        # TODO - add import info
        # TODO - add decorator info (color shape)

        for function in functions:

            # default values
            shape = 'oval'
            color = ''
            style = 'solid'

            # This function is an entrypoint
            if function.entry_point:
                shape = CALLGRAPH_ENTRYPOINT['shape']
                style = CALLGRAPH_ENTRYPOINT['style']
                color = CALLGRAPH_ENTRYPOINT['color']

            # this func is an import
            if function.is_import:
                style = CALLGRAPH_IMPORT['style']
                color = CALLGRAPH_IMPORT['color']
            self.graph.add_nodes_from([(function.offset_start,
                        {
                            "shape" : shape,
                            "style" : style,
                            "color" : color
                        })])
        nx.draw(self.graph, with_labels=True)
        plt.show()

    def _generate_call_flow_graph(self, functions):
        """
        Create all the function Node for the CallFlowGraph and call _generate_call_flow_graph_edges to build the edges
        """
        self.dot = Digraph('Call flow graph',
                           comment='Call flow graph',
                           node_attr=CALLGRAPH_NODE_ATTR,
                           graph_attr=CALLGRAPH_GRAPH_ATTR,
                           edge_attr=CALLGRAPH_EDGE_ATTR)
        self.graph = nx.Graph()
        # First, we create the nodes
        self._call_flow_graph_generate_nodes(functions)

        edges = []
        
        # build the edges btw function (nodes)
        for function in functions:
            for instr in function.instructions:
                if ("CALL" in instr.opcode):
                    offset = int(instr.id) - (PRIME - int(instr.imm))
                    if (offset < 0):
                        offset = int(instr.id) + int(instr.imm)
                    edges.append((function.offset_start, str(offset)))
        edge_labels = {}
        while (len(edges) > 0):
            self.graph.add_edge(edges[0][0], edges[0][1])
            if (edges.count(edges[0]) > 1):
                edge_labels[(edges[0][0], edges[0][1])] = edges.count(edges[0])
            edges = list(filter(lambda x: x != edges[0], edges))
        pos = nx.spring_layout(self.graph)
        mapping = {function.offset_start : function.name for function in functions}
        #self.graph = nx.relabel_nodes(self.graph, mapping, copy=False)
        nx.draw(self.graph, labels=mapping)
        nx.draw_networkx_edge_labels(self.graph, pos, edge_labels=edge_labels)
        nx.draw_networkx_edges(self.graph, pos, arrowstyle="->")
        plt.axis('off')
        plt.show()

    def print(self, view=True):
        self.dot.render(directory='output-callgraph', view=view)
        return self.dot
