# Graphical stuff for the CFG's dot
CFG_NODE_ATTR = {'style' : 'filled, solid', 'shape' : 'rect, plaintext', 'color' : "gray95", 'fontname' : "Helvetica,Arial,sans-serif"}
CFG_GRAPH_ATTR = {'overlap':'scale', 'fontname' : "Helvetica,Arial,sans-serif", 'fontsize' : '20', 'layout' : 'dot', 'newrank' : 'true'}
CFG_EDGE_ATTR = {'arrowsize':'0.5', 'fontname':"Helvetica,Arial,sans-serif", 'labeldistance':'3', 'labelfontcolor':"#00000080", 'penwidth':'2'}

# Graphical stuff for the CallFlowGraph's dot
CALLGRAPH_CONFIG = {
    'default': {
        'shape':'oval',
        'color':'',
        'style':'solid',
        'fillcolor':'white'
    },
    'entrypoint': {
        'shape':'doubleoctagon',
        'style':'filled'
    },
    'import': {
        'style':'filled',
        'fillcolor':'lightcoral'
    },
    'constructor': {
        'style':'filled',
        'fillcolor':'violet'
    },
    'l1_handler': {
        'style':'filled',
        'fillcolor':'lightskyblue'
    },
    'external': {
        'style':'filled',
        'fillcolor':'lightgreen'
    },
    'view': {
        'style':'filled',
        'fillcolor':'orange'
    },
    'raw_input': {
        'style':'filled',
        'fillcolor':'salmon'
    },
    'raw_output': {
        'style':'filled',
        'fillcolor':'tomato'
    },
    'known_ap_change': {
        'style':'filled',
        'fillcolor':'yellow'
    },
}
CALLGRAPH_NODE_ATTR = {'style' : 'filled', 'shape' : 'rect, plaintext', 'pencolor' : "#00000044", 'fontname' : "Helvetica,Arial,sans-serif"}
CALLGRAPH_GRAPH_ATTR = {'fontname' : "Helvetica,Arial,sans-serif", 'fontsize' : '20', 'layout' : 'dot', 'rankdir' : 'LR', 'newrank' : 'true'}
CALLGRAPH_EDGE_ATTR = {'arrowsize':'0.5', 'fontname':"Helvetica,Arial,sans-serif", 'labeldistance':'3', 'labelfontcolor':"#00000080", 'penwidth':'2'}

def format_print(data, end=""):
    """
    Format the print
    """
    spaces = " " * 15
    return data + spaces[len(data):] + end

# Copy from cairo-lang
# https://github.com/starkware-libs/cairo-lang/blob/167b28bcd940fd25ea3816204fa882a0b0a49603/src/starkware/cairo/lang/tracer/tracer_data.py#L261-L273
def field_element_repr(val: int, prime: int) -> str:
    """
    Converts a field element (given as int) to a decimal/hex string according to its size.
    """
    # Shift val to the range (-prime // 2, prime // 2).
    shifted_val = (val + prime // 2) % prime - (prime // 2)
    # If shifted_val is small, use decimal representation.
    if abs(shifted_val) < 2**40:
        return str(shifted_val)
    # Otherwise, use hex representation (allowing a sign if the number is close to prime).
    if abs(shifted_val) < 2**100:
        return hex(shifted_val)
    return hex(val)