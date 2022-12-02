from lark import Lark
from lark.reconstruct import Reconstructor
from typing import List

from objects import SierraFunction, SierraLibFunc, SierraStatement, SierraType

comments = []
grammar = Lark.open("sierra.lark", ambiguity="explicit", maybe_placeholders=False)

reconstructor = Reconstructor(grammar)

types: List[SierraType] = []
libfuncs: List[SierraLibFunc] = []

with open("./examples/fib.sierra", "r") as input_file:
    input_string = input_file.read()
    tree = grammar.parse(input_string)
    type_declarations = list(tree.find_data("type_declaration"))
    libfunc_declarations = list(tree.find_data("libfunc_declaration"))
    statements = list(tree.find_data("statement"))
    function = list(tree.find_data("function"))

    # Parse type declarations
    for type_declaration in type_declarations:
        # Parse type name
        concrete_type_id = list(type_declaration.find_data("concrete_type_id"))
        type_name = reconstructor.reconstruct(concrete_type_id[-1])

        types.append(SierraType(name=type_name))

    # Parse libfunc declarations
    for libfunc_declaration in libfunc_declarations:
        # Parse libfunc name
        concrete_libfunc_id = list(libfunc_declaration.find_data("concrete_libfunc_id"))
        libfunc_name = reconstructor.reconstruct(concrete_libfunc_id[-1])

        libfuncs.append(SierraLibFunc(name=libfunc_name))
