OPERATORS = {"ADD" : "+", "MUL" : "*"}
PRIME = (2**251) + (17 * (2**192)) + 1

CFG_NODE_ATTR = {'style' : 'filled, solid', 'shape' : 'rect, plaintext', 'color' : "gray95", 'fontname' : "Helvetica,Arial,sans-serif"}
CFG_GRAPH_ATTR = {'overlap':'scale', 'fontname' : "Helvetica,Arial,sans-serif", 'fontsize' : '20', 'layout' : 'dot', 'newrank' : 'true'}
CFG_EDGE_ATTR = {'arrowsize':'0.5', 'fontname':"Helvetica,Arial,sans-serif", 'labeldistance':'3', 'labelfontcolor':"#00000080", 'penwidth':'2'}

CALLGRAPH_ENTRYPOINT = {'shape' : 'doubleoctagon', 'style' : 'filled', 'color' : 'darkolivegreen1'}
CALLGRAPH_IMPORT = {'style' : 'filled', 'color' : 'lightcoral'}

CALLGRAPH_NODE_ATTR = {'style' : 'filled','shape' : 'rect', 'pencolor' : "#00000044", 'fontname' : "Helvetica,Arial,sans-serif", 'shape' : 'plaintext'}
CALLGRAPH_GRAPH_ATTR = {'fontname' : "Helvetica,Arial,sans-serif", 'fontsize' : '20', 'layout' : 'dot', 'rankdir' : 'LR', 'newrank' : 'true'}
CALLGRAPH_EDGE_ATTR = {'arrowsize':'0.5', 'fontname':"Helvetica,Arial,sans-serif", 'labeldistance':'3', 'labelfontcolor':"#00000080", 'penwidth':'2'}

def format_print(data, end=""):
    spaces = " " * 15
    return data + spaces[len(data):] + end
