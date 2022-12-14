import os

SIERRA_LARK_PARSER_PATH = os.path.realpath("./sierra/parser/sierra.lark")

# CFG Configuration
CFG_NODE_ATTR = {
    "style": "filled, solid",
    "shape": "rect, plaintext",
    "color": "gray95",
    "fontname": "Helvetica,Arial,sans-serif",
}

CFG_GRAPH_ATTR = {
    "overlap": "scale",
    "fontname": "Helvetica,Arial,sans-serif",
    "fontsize": "20",
    "layout": "dot",
    "newrank": "true",
}

CFG_EDGE_ATTR = {
    "arrowsize": "0.5",
    "fontname": "Helvetica,Arial,sans-serif",
    "labeldistance": "3",
    "labelfontcolor": "#00000080",
    "penwidth": "2",
}

# Call graph configuration
CALLGRAPH_CONFIG = {
    "default": {
        "shape": "oval",
        "color": "",
        "style": "solid",
        "fillcolor": "white",
    }
}

CALLGRAPH_NODE_ATTR = {
    "style": "filled",
    "shape": "rect, plaintext",
    "pencolor": "#00000044",
    "fontname": "Helvetica,Arial,sans-serif",
}

CALLGRAPH_GRAPH_ATTR = {
    "fontname": "Helvetica,Arial,sans-serif",
    "fontsize": "20",
    "layout": "dot",
    "rankdir": "LR",
    "newrank": "true",
}

CALLGRAPH_EDGE_ATTR = {
    "arrowsize": "0.5",
    "fontname": "Helvetica,Arial,sans-serif",
    "labeldistance": "3",
    "labelfontcolor": "#00000080",
    "penwidth": "2",
}

# User defined functions color
CALLGRAPH_USER_DEFINED_FUNCTIONS_COLOR = "lightskyblue"

# Libfunc colors
CALLGRAPH_LIBFUNCS_COLOR = "salmon"
