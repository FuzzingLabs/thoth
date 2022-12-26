import os

SIERRA_LARK_PARSER_PATH = "{}/parser/sierra.lark".format(
    os.path.dirname(os.path.realpath(__file__))
)

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

EDGE_CONDITIONAL_TRUE_COLOR = "green"
EDGE_CONDITIONAL_FALSE_COLOR = "red"
EDGE_UNCONDITIONAL_COLOR = "blue"
EDGE_FALLTHROUGH_COLOR = "black"

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
CALLGRAPH_USER_DEFINED_FUNCTIONS_COLOR = "#95D2B3"

# Libfunc colors
CALLGRAPH_LIBFUNCS_COLOR = "#E86356"
