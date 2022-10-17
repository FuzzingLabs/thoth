from typing import List
from thoth.app.decompiler.decompiler import Decompiler
from thoth.app.decompiler.variable import OperandType, Operator, Variable
from thoth.app.detectors.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)


class IntegerOverflowDetector(AbstractAnalyzer):
    """
    Detect integer overflow
    """

    NAME = "Integer overflow"
    ARGUMENT = "int_overflow"
    HELP = "Detect integer overflow"
    IMPACT: ImpactClassification = ImpactClassification.HIGH
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    CATEGORY: CategoryClassification = CategoryClassification.SECURITY

    def find_operands_values(self, root_variable: Variable) -> List:
        """
        Find a variables operands values
        e.g var3 = var2 + var1 -> [var2, var1]
        """
        all_variables = self.decompiler.ssa.memory
        local_variables = [
            variable for variable in all_variables if variable.function == root_variable.function
        ]

        operands = []

        if root_variable.value is not None:
            operands = [
                element for element in root_variable.value.operation if not element in Operator
            ]
            operands_values = [
                operand.value for operand in operands if operand.type is OperandType.VARIABLE
            ]
            # Flaten the array
            try:
                operands_values = sum(operands_values, [])
            except:
                pass

            # Related variables names
            operands_names = [
                variable for variable in local_variables if variable.name in operands_values
            ]
        return operands_names

    def _detect(self):
        contract_functions = self.disassembler.functions
        self.decompiler = Decompiler(functions=contract_functions)
        decompiled_code = self.decompiler.decompile_code()

        variables = self.decompiler.ssa.memory
        for function in contract_functions:
            # Function arguments
            arguments = set(function.arguments_list(implicit=False))
            if function.is_import:
                continue

            # Local variable in the current function scope
            local_variables = list(
                filter(lambda variable: variable.function == function, variables)
            )

            for local in local_variables:
                value = local.value
                if value is not None:
                    # If there is an addition/substraction in the variable assignation
                    if Operator.ADDITION in value.operation:

                        related_variables = self.find_operands_values(local)
                        if len(related_variables) != 2:
                            continue
                        related_variables_names = [_.name for _ in related_variables]

                        integer_overflow_variables = list(
                            set(related_variables_names).intersection(arguments)
                        )
                        # If we use one of the function argument in the assignation
                        if len(integer_overflow_variables) != 0:
                            self.detected = True
                            self.result.append(
                                "%s : %s" % (function.name, integer_overflow_variables[0])
                            )
