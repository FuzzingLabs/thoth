# Graphical stuff for the CFG's dot

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

# Graphical stuff for the CallFlowGraph's dot
CALLGRAPH_CONFIG = {
    "default": {
        "shape": "oval",
        "color": "",
        "style": "solid",
        "fillcolor": "white",
    },
    "entrypoint": {"shape": "doubleoctagon", "style": "filled"},
    "import": {"style": "filled", "fillcolor": "lightcoral"},
    "constructor": {"style": "filled", "fillcolor": "violet"},
    "l1_handler": {"style": "filled", "fillcolor": "lightskyblue"},
    "external": {"style": "filled", "fillcolor": "lightgreen"},
    "view": {"style": "filled", "fillcolor": "orange"},
    "raw_input": {"style": "filled", "fillcolor": "salmon"},
    "raw_output": {"style": "filled", "fillcolor": "tomato"},
    "known_ap_change": {"style": "filled", "fillcolor": "yellow"},
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
