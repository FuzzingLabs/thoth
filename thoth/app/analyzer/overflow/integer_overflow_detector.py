from thoth.app.decompiler.decompiler import Decompiler
from thoth.app.decompiler.variable import OperandType, Operator, Variable, VariableValueType
from thoth.app.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
)
from thoth.app.dfg.dfg import DFG


class IntegerOverflowDetector(AbstractAnalyzer):
    """
    Detect integer overflow
    """

    NAME = "Integer overflow"
    ARGUMENT = "int_overflow"
    HELP = "Detect direct integer overflow/underflow"
    IMPACT: ImpactClassification = ImpactClassification.HIGH
    PRECISION: PrecisionClassification = PrecisionClassification.MEDIUM
    CATEGORY: CategoryClassification = CategoryClassification.SECURITY

    def _detect(self):
        if self.disassembler.cairo1:
            return False

        contract_functions = self.disassembler.functions

        self.decompiler = Decompiler(functions=contract_functions)
        self.decompiler.decompile_code(first_pass_only=True, imported_functions=False)

        dfg = DFG(self.decompiler.ssa.memory)
        dfg._create_dfg()
        dfg._taint_functions_arguments()

        variables = self.decompiler.ssa.memory
        for function in contract_functions:
            # Function arguments
            arguments = set(function.arguments_list(implicit=False, ret=False))
            if function.is_import:
                continue

            # Local variable in the current function scope
            local_variables = list(
                filter(lambda variable: variable.function == function, variables)
            )

            for local in local_variables:
                value = local.value
                if value is None:
                    continue

                # TODO : Handle variables assigned by a function call
                if value.type == VariableValueType.FUNCTION_CALL:
                    continue

                operands = [v for v in value.operation if not isinstance(v, Operator)]
                variables_operands = [o for o in operands if o.type == OperandType.VARIABLE]
                variables_operands_values = [o.value for o in variables_operands]

                if len(variables_operands) != 2:
                    continue

                # Use DFG to find tainted variables
                try:
                    dfg_variable = [
                        v
                        for v in dfg.variables_blocks
                        if v.name in variables_operands_values[1] and v.function == function
                    ][0]
                except:
                    continue
                # Direct integer overflow
                if dfg_variable.tainting_coefficient == 1:
                    self.detected = True
                    self.result.append("%s : %s" % (function.name, dfg_variable.name))
                # Indirect integer overflow
                elif dfg_variable.tainting_coefficient >= 0.7:
                    # Less critical than direct integer overflow/underflow
                    self.IMPACT = ImpactClassification.MEDIUM
                    self.detected = True
                    self.result.append("%s : %s (indirect)" % (function.name, dfg_variable.name))
