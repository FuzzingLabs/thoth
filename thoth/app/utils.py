import sys
import yaml
from typing import List


class bcolors:
    def __init__(self, color=False):
        self.HEADER = "\033[95m" if color else ""
        self.BLUE = "\033[94m" if color else ""
        self.CYAN = "\033[96m" if color else ""
        self.GREEN = "\033[92m" if color else ""
        self.YELLOW = "\033[93m" if color else ""
        self.RED = "\033[91m" if color else ""
        self.ENDC = "\033[0m" if color else ""
        self.BOLD = "\033[1m" if color else ""
        self.BEIGE = "\033[36m" if color else ""
        self.UNDERLINE = "\033[4m" if color else ""


class Kosaraju:
    """
    Kosaraju's Algorithm is used for finding strongly connected components
    in a directed graph
    """

    def __init__(self, graph: List[List]) -> None:
        self.graph = graph
        self.size = len(self.graph)

        self.visited = [False] * self.size
        self.graph_vertices_ordered = [0] * self.size
        self.visited_vertices = self.size
        self.transpose_graph = [[]] * self.size

    def connected_components(self) -> int:
        """
        Find all connected components in a graph
        """
        # Visit each vertex of the graph
        for vertex in range(len(self.graph)):
            self.visit(vertex)

        self.connected_components = [0] * self.size

        for vertex in self.graph_vertices_ordered:
            self.assign(vertex, vertex)

        return self.connected_components

    def visit(self, vertex: int) -> None:
        """
        Visit a graph vertex
        """
        if not self.visited[vertex]:
            self.visited[vertex] = True
            # Visit all adjacents vertices
            for v in self.graph[vertex]:
                self.visit(v)
                self.transpose_graph[v] = self.transpose_graph[v] + [vertex]

            self.visited_vertices = self.visited_vertices - 1
            self.graph_vertices_ordered[self.visited_vertices] = vertex

    def assign(self, vertex: int, root: int) -> None:
        """
        Assign a vertex
        """
        if self.visited[vertex]:
            self.visited[vertex] = False
            self.connected_components[vertex] = root
            for transpose_graph_vertex in self.transpose_graph[vertex]:
                self.assign(transpose_graph_vertex, root)


def globals():
    global color
    color = bcolors()


# Copy from cairo-lang
# https://github.com/starkware-libs/cairo-lang/blob/167b28bcd940fd25ea3816204fa882a0b0a49603/src/starkware/cairo/lang/tracer/tracer_data.py#L261-L273
def field_element_repr(val: int, prime: int) -> str:
    """Converts a field element (given as int) to a decimal/hex string according to its size.


    Args:
        val (int): The value
        prime (int): The prime

    Returns:
        str: The hex value
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


def value_to_string(val: int, prime: int) -> str:
    """Check if the imm value is a printable string to add it as a comment

    Args:
        val (int): The value
        prime (int): The prime

    Returns:
        str: The string representation
    """
    repr = field_element_repr(val, prime)
    repr_hex = ""
    # print(f"here {bytearray.fromhex(repr[2:])} end")
    if repr[:2] != "0x":
        try:
            repr_hex = hex(int(repr))
        except Exception:
            return ""
    else:
        return ""
    try:
        repr_str = bytearray.fromhex(repr_hex[2:]).decode("utf-8")
        if not repr_str.isprintable():
            return hex(int(repr))
        return repr_str
    except Exception:
        return repr_hex


def load_symbex_yaml_config(yaml_file: str) -> dict:
    """
    Load a symbolic execution config from a YAML file
    """

    yaml_data = yaml.safe_load(yaml_file)

    function = yaml_data["function"]
    constraints = yaml_data["constraints"] if "constraints" in yaml_data else []
    variables = yaml_data["variables"] if "variables" in yaml_data else []
    solves = yaml_data["solves"]

    symbex_config = {
        "function": function,
        "constraints": constraints,
        "variables": variables,
        "solves": solves,
    }
    return symbex_config
