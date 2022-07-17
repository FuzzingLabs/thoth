from graphviz import Digraph
from utils import field_element_repr, CALLGRAPH_CONFIG, CALLGRAPH_NODE_ATTR, CALLGRAPH_GRAPH_ATTR, CALLGRAPH_EDGE_ATTR
class CallFlowGraph:
    """
    CallFlowGraph class

    Create a call flow graph for the contract
    """
    def __init__(self, functions, config=CALLGRAPH_CONFIG):
        self.dot = None
        self.config = config
        self._generate_call_flow_graph(functions)


    def _call_flow_graph_generate_nodes(self, functions):
        """
        Create all the function nodes
        """
        # TODO - issue #47

        for function in functions:

            # Default values
            shape = self.config['default']['shape']
            color = self.config['default']['color']
            style = self.config['default']['style']
            fillcolor=self.config['default']['fillcolor']

            label=function.name

            # This function is an entrypoint
            if function.entry_point:
                shape=self.config['entrypoint']['shape']
                style=self.config['entrypoint']['style']

            # Node color selection by priority
            # This function is an import
            if function.is_import:
                style=self.config['import']['style']
                fillcolor=self.config['import']['fillcolor']

            elif 'constructor' in function.decorators:
                style=self.config['constructor']['style']
                fillcolor=self.config['constructor']['fillcolor']

            elif 'l1_handler' in function.decorators:
                style=self.config['l1_handler']['style']
                fillcolor=self.config['l1_handler']['fillcolor']

            elif 'external' in function.decorators:
                style=self.config['external']['style']
                fillcolor=self.config['external']['fillcolor']

            elif 'view' in function.decorators:
                style=self.config['view']['style']
                fillcolor=self.config['view']['fillcolor']

            elif 'raw_input' in function.decorators:
                style=self.config['raw_input']['style']
                fillcolor=self.config['raw_input']['fillcolor']

            elif 'raw_output' in function.decorators:
                style=self.config['raw_output']['style']
                fillcolor=self.config['raw_output']['fillcolor']

            elif 'known_ap_change' in function.decorators:
                style=self.config['known_ap_change']['style']
                fillcolor=self.config['known_ap_change']['fillcolor']

            # Search if this function is doing indirect_calls
            if any(inst.is_call_indirect() for inst in function.instructions):
                label+=' **'

            # Add decorator below the function name
            if function.decorators != []:
                label+=f'\\l{str(function.decorators)}'


            # Create the function node
            self.dot.node(function.offset_start,
                                 label=label,
                                 shape=shape,
                                 style=style,
                                 color=color,
                                 fillcolor=fillcolor)


    def _generate_call_flow_graph(self, functions):
        """
        Create the complete CallFlowGraph's dot
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
                        edges.append((function.offset_start, inst.call_offset))
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
