OPERATORS = {"ADD" : "+", "MUL" : "*"}
PRIME = (2**251) + (17 * (2**192)) + 1

NODE_ATTR = {'style' : 'filled','shape' : 'rect', 'pencolor' : "#00000044", 'fontname' : "Helvetica,Arial,sans-serif", 'shape' : 'plaintext'}
GRAPH_ATTR = {'fontname' : "Helvetica,Arial,sans-serif", 'fontsize' : '20', 'layout' : 'dot', 'rankdir' : 'LR', 'newrank' : 'true'}
EDGE_ATTR = {'arrowsize':'0.5', 'fontname':"Helvetica,Arial,sans-serif", 'labeldistance':'3', 'labelfontcolor':"#00000080", 'penwidth':'2'}

def format_print(data, end=""):
    spaces = " " * 15
    return data + spaces[len(data):] + end
