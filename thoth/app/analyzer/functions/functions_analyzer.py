from thoth.app.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
    colors,
)


class FunctionsAnalyzer(AbstractAnalyzer):
    """
    Detect strings inside a contract
    """

    NAME = "Functions"
    ARGUMENT = "functions"
    HELP = "Retrieve informations about the contract's functions"
    IMPACT: ImpactClassification = ImpactClassification.NONE
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    CATEGORY: CategoryClassification = CategoryClassification.INFORMATIONAL

    def _detect(self) -> None:
        contract_functions = [
            function for function in self.disassembler.functions if not function.is_import
        ]
        self.detected = bool(contract_functions)

        for function in contract_functions:
            # Function name
            function_path = function.name.split(".")
            if len(function_path) == 2 and function_path[0] == "__main__":
                function_name = function_path[1]
            else:
                function_name = function.name
            result = colors.HEADER + function_name + colors.ENDC

            interact_with_L1 = False
            # Send messages to L1
            for instruction in function.instructions:
                if "CALL" in instruction.opcode:
                    if instruction.is_call_direct() and instruction.call_xref_func_name is not None:
                        call_name = instruction.call_xref_func_name.split(".")[-1]
                        if call_name == "send_message_to_l1":
                            result += colors.CYAN + " -> L1" + colors.ENDC
                            interact_with_L1 = True

            decorators = [decorator for decorator in function.decorators]

            # Receive messages from L1
            if decorators:
                if "l1_handler" in decorators:
                    result += colors.YELLOW + " <- L1" + colors.ENDC
                    interact_with_L1 = True

            # Decorators list
            if decorators:
                result += "\n"
                result += "\t- decorators : %s" % ", ".join(decorators)

            self.result.append(result)
