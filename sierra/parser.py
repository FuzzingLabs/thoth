from lark import Lark

grammar = Lark.open("sierra.lark")

with open("./examples/fib_array.sierra", "r") as input_file:
    input_string = input_file.read()
    tree = grammar.parse(input_string)

    type_declarations = list(tree.find_data("type_declaration"))
    libfunc_declarations = list(tree.find_data("libfunc_declaration"))
    statements = list(tree.find_data("statement"))
    function = list(tree.find_data("function"))