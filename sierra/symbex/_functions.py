import re
import z3

from typing import List, Optional
from z3 import And, Not, Or, Xor


def felt_const(
    self,
    function_name: str,
    assigned_variables: List[z3.z3.BitVecRef],
    function_arguments: List[z3.z3.BitVecRef],
) -> Optional[z3.z3.BoolRef]:
    """
    Convert felt_const function call to a Z3 constraint
    """
    function_regexp = r"([a-z0-9])+?_const<([0-9]+)>"

    match_function = re.match(function_regexp, function_name)
    if match_function is None:
        return None

    variable = assigned_variables[0]
    const_value = int(match_function.group(2))

    return self.solver.add(variable == const_value)


def felt_sub(
    self,
    function_name: str,
    assigned_variables: List[z3.z3.BitVecRef],
    function_arguments: List[z3.z3.BitVecRef],
) -> Optional[z3.z3.BoolRef]:
    """
    Convert felt_sub function call to a Z3 constraint
    """
    function_regexp = r"felt(252)?_sub"

    if not re.match(function_regexp, function_name):
        return None

    variable = assigned_variables[0]

    return self.solver.add(variable == function_arguments[0] - function_arguments[1])


def felt_div(
    self,
    function_name: str,
    assigned_variables: List[z3.z3.BitVecRef],
    function_arguments: List[z3.z3.BitVecRef],
) -> Optional[z3.z3.BoolRef]:
    """
    Convert felt_div function call to a Z3 constraint
    """
    function_regexp = r"felt(252)?_div"

    if not re.match(function_regexp, function_name):
        return None

    variable = assigned_variables[0]

    return self.solver.add(variable == function_arguments[0] / function_arguments[1])


def felt_mul(
    self,
    function_name: str,
    assigned_variables: List[z3.z3.BitVecRef],
    function_arguments: List[z3.z3.BitVecRef],
) -> Optional[z3.z3.BoolRef]:
    """
    Convert felt_mul function call to a Z3 constraint
    """
    function_regexp = r"felt(252)?_mul"

    if not re.match(function_regexp, function_name):
        return None

    variable = assigned_variables[0]

    return self.solver.add(variable == function_arguments[0] / function_arguments[1])


def felt_add(
    self,
    function_name: str,
    assigned_variables: List[z3.z3.BitVecRef],
    function_arguments: List[z3.z3.BitVecRef],
) -> Optional[z3.z3.BoolRef]:
    """
    Convert felt_add function call to a Z3 constraint
    """
    function_regexp = r"felt(252)?_add"

    if not re.match(function_regexp, function_name):
        return None

    variable = assigned_variables[0]
    return self.solver.add(variable == function_arguments[0] + function_arguments[1])


def bool_or(
    self,
    function_name: str,
    assigned_variables: List[z3.z3.BitVecRef],
    function_arguments: List[z3.z3.BitVecRef],
) -> Optional[z3.z3.BoolRef]:
    """
    Convert bool_or function call to a Z3 constraint
    """
    if not function_name.startswith("bool_or"):
        return None

    variable = assigned_variables[0]
    return self.solver.add(variable == function_arguments[0] | function_arguments[1])


def bool_xor(
    self,
    function_name: str,
    assigned_variables: List[z3.z3.BitVecRef],
    function_arguments: List[z3.z3.BitVecRef],
) -> Optional[z3.z3.BoolRef]:
    """
    Convert bool_xor function call to a Z3 constraint
    """
    if not function_name.startswith("bool_xor"):
        return None

    variable = assigned_variables[0]
    return self.solver.add(variable == function_arguments[0] ^ function_arguments[1])


def bool_and(
    self,
    function_name: str,
    assigned_variables: List[z3.z3.BitVecRef],
    function_arguments: List[z3.z3.BitVecRef],
) -> Optional[z3.z3.BoolRef]:
    """
    Convert bool_and function call to a Z3 constraint
    """
    if not function_name.startswith("bool_and"):
        return None

    variable = assigned_variables[0]
    return self.solver.add(variable == function_arguments[0] & function_arguments[1])


def storetemp(
    self,
    function_name: str,
    assigned_variables: List[z3.z3.BitVecRef],
    function_arguments: List[z3.z3.BitVecRef],
) -> Optional[z3.z3.BoolRef]:
    """
    Convert store_temp function call to a Z3 constraint
    """

    if not function_name.startswith("store_temp"):
        return None

    variable = assigned_variables[0]
    return self.solver.add(variable == function_arguments[0])


def dup(
    self,
    function_name: str,
    assigned_variables: List[z3.z3.BitVecRef],
    function_arguments: List[z3.z3.BitVecRef],
) -> Optional[z3.z3.BoolRef]:
    """
    Convert dup function call to a Z3 constraint
    """

    if not function_name.startswith("dup"):
        return None

    variable = assigned_variables[1]
    return self.solver.add(variable == function_arguments[0])


def rename(
    self,
    function_name: str,
    assigned_variables: List[z3.z3.BitVecRef],
    function_arguments: List[z3.z3.BitVecRef],
) -> Optional[z3.z3.BoolRef]:
    """
    Convert rename function call to a Z3 constraint
    """

    if not function_name.startswith("rename"):
        return None

    variable = assigned_variables[0]
    return self.solver.add(variable == function_arguments[0])
