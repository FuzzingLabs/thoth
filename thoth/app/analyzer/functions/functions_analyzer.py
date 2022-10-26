from thoth.app.analyzer.abstract_analyzer import (
    AbstractAnalyzer,
    CategoryClassification,
    ImpactClassification,
    PrecisionClassification,
    colors,
)


class FunctionsAnalyzer(AbstractAnalyzer):
    """
    Analyze a contract functions
    """

    NAME = "Functions"
    ARGUMENT = "functions"
    HELP = "Retrieve informations about the contract's functions"
    IMPACT: ImpactClassification = ImpactClassification.INFORMATIONAL
    PRECISION: PrecisionClassification = PrecisionClassification.HIGH
    CATEGORY: CategoryClassification = CategoryClassification.ANALYTICS

    def _detect(self) -> None:
        # Colors
        header_color = colors.HEADER if self.color else ""
        red_color = colors.RED if self.color else ""
        cyan_color = colors.CYAN if self.color else ""
        yellow_color = colors.YELLOW if self.color else ""
        end_color = colors.ENDC if self.color else ""

        contract_functions = [
            function for function in self.disassembler.functions if not function.is_import
        ]
        self.detected = bool(contract_functions)

        for function in contract_functions:
            # Function ID
            function_id = str(function.id)
            result = "(%s) " % function_id

            # Function name
            function_path = function.name.split(".")
            if len(function_path) == 2 and function_path[0] == "__main__":
                function_name = function_path[1]
            else:
                function_name = function.name
            result += header_color + function_name + end_color

            interact_with_L1 = False
            # Send messages to L1
            for instruction in function.instructions:
                if "CALL" in instruction.opcode:
                    if instruction.is_call_direct() and instruction.call_xref_func_name is not None:
                        call_name = instruction.call_xref_func_name.split(".")[-1]
                        if call_name == "send_message_to_l1":
                            result += cyan_color + " -> L1" + end_color
                            interact_with_L1 = True

            decorators = [decorator for decorator in function.decorators]

            # Receive messages from L1
            if decorators:
                if "l1_handler" in decorators:
                    result += yellow_color + " <- L1" + end_color
                    interact_with_L1 = True

            # Entry points
            if function.entry_point:
                result += red_color + " (entry point)" + end_color

            # Decorators list
            if decorators:
                result += "\n"
                result += "\t- decorators : %s" % ", ".join(decorators)

            # Cyclomatic complexity
            cyclomatic_complexity = function.cyclomatic_complexity
            result += "\n"
            result += "\t- cyclomatic complexity : %s" % cyclomatic_complexity

            # Instructions count
            instructions_count = len(function.instructions)
            result += "\n"
            result += "\t- instructions : %s" % instructions_count

            self.result.append(result)
