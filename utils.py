operator = {"ADD" : "+", "MUL" : "*"}
prime = (2**251) + (17 * (2**192)) + 1

def fPrint(data, end="\n"):
    spaces = " " * 15
    print(data + spaces[len(data):], end=end)
    
def has_edge(graph, v1, v2):
    tail_name = graph._quote_edge(v1)
    head_name = graph._quote_edge(v2)
    return (graph._edge % (tail_name, head_name, '')) in graph.body