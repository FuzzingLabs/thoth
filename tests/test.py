import glob
import os
import sys
import unittest

import thoth.app.analyzer as analyzer
from thoth.app.analyzer import all_analyzers
from thoth.app.analyzer.abstract_analyzer import ImpactClassification
from thoth.app.decompiler.decompiler import Decompiler
from thoth.app.dfg.dfg import DFG, Tainting
from thoth.app.disassembler.disassembler import Disassembler
from thoth.app.symbex.symbex import SymbolicExecution


class TestDisassembler(unittest.TestCase):
    """
    Testing class
    """

    def test_disassembler_no_file_should_crash(self):
        """
        Test the disassembler on all files
        """
        all_test = glob.glob("./tests/json_files/cairo_0/*")
        crash = 0
        f = open("/dev/null", "w")
        save_stdout = sys.stdout
        sys.stdout = f
        for test in all_test:
            try:
                disassembler = Disassembler(test)
                disassembler.print_disassembly()
                filename = os.path.basename(test).split(".")[0]
                format = "pdf"
                disassembler.print_call_flow_graph(
                    folder="output_graph",
                    filename=filename,
                    format=format,
                    view=False,
                )
            except Exception as e:
                sys.stderr.write(str(e))
                crash += 1
            except SystemExit as e:
                sys.stderr.write(test + "\n")
                sys.stderr.write(str(e) + "\n")
                crash += 1
        sys.stdout = save_stdout
        f.close()
        self.assertEqual(crash, 0)

    def test_no_analyzer_should_crash(self):
        """
        Test all analyzers
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/cairo_amm.json")
        crash = 0

        for a in all_analyzers:
            try:
                a(disassembler)._detect()
            except:
                print(a)
                crash += 1
        self.assertEqual(crash, 0)

    def test_cairo_return_statistics_analyzer(self):
        """
        Test the functions analyzer on cairo_return
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/cairo_return.json")
        statistics_analyzer = analyzer.StatisticsAnalyzer(disassembler, color=False)
        statistics_analyzer._detect()

        self.assertEqual(statistics_analyzer.result[0], "functions : 2")
        self.assertEqual(statistics_analyzer.result[1], "builtins : 0")
        self.assertEqual(statistics_analyzer.result[2], "structs : 6")
        self.assertEqual(statistics_analyzer.result[3], "calls : 2")

    def test_cairo_all_builtins_statistics_analyzer(self):
        """
        Test the statistics analyzer on cairo_all_builtins
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/cairo_all_builtins.json")
        statistics_analyzer = analyzer.StatisticsAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(statistics_analyzer.result[0], "functions : 1")
        self.assertEqual(statistics_analyzer.result[1], "builtins : 4")
        self.assertEqual(statistics_analyzer.result[2], "structs : 8")
        self.assertEqual(statistics_analyzer.result[3], "calls : 0")

    def test_cairo_all_builtins_functions_analyzer(self):
        """
        Test the functions analyzer on cairo_all_builtins
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/cairo_all_builtins.json")
        functions_analyzer = analyzer.FunctionsAnalyzer(disassembler, color=False)
        functions_analyzer._detect()

        self.assertEqual(
            functions_analyzer.result[0],
            "(0) main (entry point)\n\t- cyclomatic complexity : 2\n\t- instructions : 1",
        )

    def test_cairo_direct_and_indirect_recursion_statistics_analyzer(self):
        """
        Test the statistics analyzer on cairo_direct_and_indirect_recursion
        """
        disassembler = Disassembler(
            "./tests/json_files/cairo_0/cairo_direct_and_indirect_recursion.json"
        )
        statistics_analyzer = analyzer.StatisticsAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(statistics_analyzer.result[0], "functions : 5")
        self.assertEqual(statistics_analyzer.result[1], "builtins : 0")
        self.assertEqual(statistics_analyzer.result[2], "structs : 15")
        self.assertEqual(statistics_analyzer.result[3], "calls : 10")

    def test_cairo_direct_and_indirect_recursion_functions_analyzer(self):
        """
        Test the functions analyzer on cairo_direct_and_indirect_recursion
        """
        disassembler = Disassembler(
            "./tests/json_files/cairo_0/cairo_direct_and_indirect_recursion.json"
        )
        functions_analyzer = analyzer.FunctionsAnalyzer(disassembler, color=False)
        functions_analyzer._detect()

        self.assertEqual(
            functions_analyzer.result[0],
            "(0) a\n\t- cyclomatic complexity : 9\n\t- instructions : 6",
        )
        self.assertEqual(
            functions_analyzer.result[1],
            "(1) b\n\t- cyclomatic complexity : 8\n\t- instructions : 6",
        )
        self.assertEqual(
            functions_analyzer.result[2],
            "(2) c\n\t- cyclomatic complexity : 8\n\t- instructions : 6",
        )
        self.assertEqual(
            functions_analyzer.result[3],
            "(3) d\n\t- cyclomatic complexity : 8\n\t- instructions : 6",
        )
        self.assertEqual(
            functions_analyzer.result[4],
            "(4) main (entry point)\n\t- cyclomatic complexity : 8\n\t- instructions : 6",
        )

    def test_cairo_struct_statistics_analyzer(self):
        """
        Test the statistics analyzer on cairo_struct
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/cairo_struct.json")
        statistics_analyzer = analyzer.StatisticsAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(statistics_analyzer.result[0], "functions : 1")
        self.assertEqual(statistics_analyzer.result[1], "builtins : 0")
        self.assertEqual(statistics_analyzer.result[2], "structs : 4")
        self.assertEqual(statistics_analyzer.result[3], "calls : 0")

    def test_cairo_puzzle_statistics_analyzer(self):
        """
        Test statistics analyzer on test_cairo_puzzle
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/cairo_puzzle.json")
        statistics_analyzer = analyzer.StatisticsAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(statistics_analyzer.result[0], "functions : 18")
        self.assertEqual(statistics_analyzer.result[1], "builtins : 2")
        self.assertEqual(statistics_analyzer.result[2], "structs : 59")
        self.assertEqual(statistics_analyzer.result[3], "calls : 30")

    def test_starknet_decorators3_statistics_analyzer(self):
        """
        Test statistics analyzer on test_starknet_decorators3
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/starknet_decorators3.json")
        statistics_analyzer = analyzer.StatisticsAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(statistics_analyzer.result[0], "functions : 15")
        self.assertEqual(statistics_analyzer.result[1], "builtins : 2")
        self.assertEqual(statistics_analyzer.result[2], "structs : 88")
        self.assertEqual(statistics_analyzer.result[3], "calls : 18")

    def test_starknet_decorators3_functions_analyzer(self):
        """
        Test the decorators output of the functions analyzer on starknet_decorators3
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/starknet_decorators3.json")
        functions_analyzer = analyzer.FunctionsAnalyzer(disassembler, color=False)
        functions_analyzer._detect()

        self.assertEqual(
            functions_analyzer.result[0],
            "(7) __main__.balance.addr\n\t- cyclomatic complexity : 1\n\t- instructions : 11",
        )
        self.assertEqual(
            functions_analyzer.result[1],
            "(8) __main__.balance.read\n\t- cyclomatic complexity : 1\n\t- instructions : 12",
        )
        self.assertEqual(
            functions_analyzer.result[2],
            "(9) __main__.balance.write\n\t- cyclomatic complexity : 1\n\t- instructions : 11",
        )
        self.assertEqual(
            functions_analyzer.result[3],
            "(10) increase_balance\n\t- decorators : external\n\t- cyclomatic complexity : 1\n\t- instructions : 17",
        )
        self.assertEqual(
            functions_analyzer.result[4],
            "(11) __wrappers__.increase_balance (entry point)\n\t- decorators : external\n\t- cyclomatic complexity : 1\n\t- instructions : 14",
        )
        self.assertEqual(
            functions_analyzer.result[5],
            "(12) get_balance\n\t- decorators : view\n\t- cyclomatic complexity : 1\n\t- instructions : 6",
        )
        self.assertEqual(
            functions_analyzer.result[6],
            "(13) __wrappers__.get_balance_encode_return\n\t- cyclomatic complexity : 1\n\t- instructions : 7",
        )
        self.assertEqual(
            functions_analyzer.result[7],
            "(14) __wrappers__.get_balance (entry point)\n\t- decorators : view\n\t- cyclomatic complexity : 1\n\t- instructions : 15",
        )

    def test_starknet_l1_default_statistics_analyzer(self):
        """
        Test the statistics analyzer on starknet_l1_default
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/starknet_l1_default.json")
        statistics_analyzer = analyzer.StatisticsAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(statistics_analyzer.result[0], "functions : 13")
        self.assertEqual(statistics_analyzer.result[1], "builtins : 3")
        self.assertEqual(statistics_analyzer.result[2], "structs : 79")
        self.assertEqual(statistics_analyzer.result[3], "calls : 12")

    def test_starknet_l1_default_functions_analyzer(self):
        """
        Test the Layer 1 interactions output on starknet_l1_default
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/starknet_l1_default.json")
        functions_analyzer = analyzer.FunctionsAnalyzer(disassembler, color=False)
        functions_analyzer._detect()

        self.assertEqual(
            functions_analyzer.result[0],
            "(4) __main__.impl_address.addr\n\t- cyclomatic complexity : 1\n\t- instructions : 4",
        )
        self.assertEqual(
            functions_analyzer.result[1],
            "(5) __main__.impl_address.read\n\t- cyclomatic complexity : 1\n\t- instructions : 11",
        )
        self.assertEqual(
            functions_analyzer.result[2],
            "(6) __main__.impl_address.write\n\t- cyclomatic complexity : 1\n\t- instructions : 10",
        )
        self.assertEqual(
            functions_analyzer.result[3],
            "(7) constructor\n\t- decorators : external\n\t- cyclomatic complexity : 1\n\t- instructions : 6",
        )
        self.assertEqual(
            functions_analyzer.result[4],
            "(8) __wrappers__.constructor (entry point)\n\t- decorators : external\n\t- cyclomatic complexity : 1\n\t- instructions : 15",
        )
        self.assertEqual(
            functions_analyzer.result[5],
            "(9) __default__\n\t- decorators : external, raw_input, raw_output\n\t- cyclomatic complexity : 1\n\t- instructions : 16",
        )
        self.assertEqual(
            functions_analyzer.result[6],
            "(10) __wrappers__.__default__ (entry point)\n\t- decorators : external, raw_input, raw_output\n\t- cyclomatic complexity : 1\n\t- instructions : 14",
        )
        self.assertEqual(
            functions_analyzer.result[7],
            "(11) __l1_default__ <- L1\n\t- decorators : l1_handler, raw_input\n\t- cyclomatic complexity : 1\n\t- instructions : 14",
        )
        self.assertEqual(
            functions_analyzer.result[8],
            "(12) __wrappers__.__l1_default__ <- L1 (entry point)\n\t- decorators : l1_handler, raw_input\n\t- cyclomatic complexity : 1\n\t- instructions : 15",
        )

    def test_starknet_get_code_l2_dai_bridge_statistics_analyzer(self):
        """
        Test the statistics analyzer on starknet_get_code_l2_dai_bridge
        """
        disassembler = Disassembler(
            "./tests/json_files/cairo_0/starknet_get_code_l2_dai_bridge.json"
        )
        statistics_analyzer = analyzer.StatisticsAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(statistics_analyzer.result[0], "functions : 1")
        self.assertEqual(statistics_analyzer.result[1], "builtins : 0")
        self.assertEqual(statistics_analyzer.result[2], "structs : 0")
        self.assertEqual(statistics_analyzer.result[3], "calls : 135")

    def test_starknet_send_message_to_l1_functions_analyzer(self):
        """
        Test Layer 1 interactions output on starknet_send_message_to_l1
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/starknet_send_message_to_l1.json")
        functions_analyzer = analyzer.FunctionsAnalyzer(disassembler, color=False)
        functions_analyzer._detect()

        self.assertEqual(
            functions_analyzer.result[0],
            "(2) generate -> L1\n\t- decorators : external\n\t- cyclomatic complexity : 1\n\t- instructions : 12",
        )
        self.assertEqual(
            functions_analyzer.result[1],
            "(3) __wrappers__.generate (entry point)\n\t- decorators : external\n\t- cyclomatic complexity : 1\n\t- instructions : 11",
        )

    def test_starknet_erc20_analyzer(self):
        """
        Test the ERC20 analyzer
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/starknet_erc20.json")
        functions_analyzer = analyzer.ERC20Analyzer(disassembler, color=False)
        functions_analyzer._detect()

        self.assertEqual(functions_analyzer.detected, True)

    def test_starknet_erc721_analyzer(self):
        """
        Test the ERC721 analyzer
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/starknet_erc721.json")
        functions_analyzer = analyzer.ERC721Analyzer(disassembler, color=False)
        functions_analyzer._detect()

        self.assertEqual(functions_analyzer.detected, True)

    def test_cairo_integer_overflow_integer_overflow_detector(self):
        """
        Test the Integer Overflow Detector
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/cairo_integer_overflow.json")
        integer_overflow_detector = analyzer.IntegerOverflowDetector(disassembler, color=False)
        integer_overflow_detector._detect()

        self.assertEqual(integer_overflow_detector.detected, True)

    def test_cairo_integer_overflow_integer_2_overflow_detector(self):
        """
        Test the Integer Overflow Detector
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/cairo_integer_overflow_2.json")
        integer_overflow_detector = analyzer.IntegerOverflowDetector(disassembler, color=False)
        integer_overflow_detector._detect()

        self.assertEqual(integer_overflow_detector.detected, True)
        self.assertEqual(integer_overflow_detector.IMPACT, ImpactClassification.MEDIUM)

    def test_cairo_integer_overflow_dfg(self):
        """
        Test the DFG on cairo_integer_overflow
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/cairo_integer_overflow.json")
        decompiler = Decompiler(functions=disassembler.functions)
        decompiler.decompile_code(first_pass_only=True, imported_functions=False)

        dfg = DFG(decompiler.ssa.memory)
        dfg._create_dfg()
        dfg._create_graph_representation()

        # Find v1
        v1 = [v for v in dfg.variables_blocks if v.name == "v9"][0]
        v1_parents = [parent.name for parent in v1.parents_blocks]
        self.assertEqual(["v8", "v5_integer"], v1_parents)

        # Find v5
        v5 = [v for v in dfg.variables_blocks if v.name == "v11"][0]
        v5_parents = [parent.name for parent in v5.parents_blocks]
        self.assertEqual(["v9"], v5_parents)

    def test_cairo_integer_overflow_2_tainting_dfg(self):
        """
        Test the DFG tainting on cairo_integer_overflow_2
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/cairo_integer_overflow_2.json")
        decompiler = Decompiler(functions=disassembler.functions)
        decompiler.decompile_code(first_pass_only=True, imported_functions=False)

        dfg = DFG(decompiler.ssa.memory)
        dfg._create_dfg()
        dfg._create_graph_representation()
        dfg._taint_functions_arguments()

        # Find v1
        v1 = [v for v in dfg.variables_blocks if v.name == "v9"][0]
        self.assertEqual(1 * Tainting.PROPAGATION_COEFFICIENT, v1.tainting_coefficient)
        # Find v3
        v3 = [v for v in dfg.variables_blocks if v.name == "v10"][0]
        self.assertEqual(1 * Tainting.PROPAGATION_COEFFICIENT**2, v3.tainting_coefficient)
        # Find v6
        v6 = [v for v in dfg.variables_blocks if v.name == "v12"][0]
        self.assertEqual(1 * Tainting.PROPAGATION_COEFFICIENT**3, v6.tainting_coefficient)

    def test_starknet_get_code_l2_dai_bridge_functions_naming_analyzer(self):
        """
        Test the variable naming analyzer on starknet_get_code_l2_dai_bridge
        """
        disassembler = Disassembler(
            "./tests/json_files/cairo_0/starknet_get_full_contract_l2_dai_bridge.json"
        )
        statistics_analyzer = analyzer.FunctionNamingAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(
            statistics_analyzer.result[0], "balanceOf function name needs to be in snake case"
        )
        self.assertEqual(
            statistics_analyzer.result[1], "get_L1_address function name needs to be in snake case"
        )

    def test_erc20_mintable_variable_naming_analyzer(self):
        """
        Test the variable naming analyzer on erc20_mintable
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/starknet_erc20_mintable.json")
        statistics_analyzer = analyzer.VariableNamingAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(
            statistics_analyzer.result[0],
            "newOwner argument name (transferOwnership function) needs to be in snake case",
        )

    def test_test_cases_generator_analyzer(self):
        """
        Test the test cases generator analyzer on test_symbolic_execution_2
        """
        disassembler = Disassembler(
            "./tests/json_files/cairo_0/cairo_test_symbolic_execution_2.json"
        )
        contract_functions = disassembler.functions
        decompiler = Decompiler(functions=contract_functions)
        decompiler.decompile_code(first_pass_only=True)

        symbex = SymbolicExecution(variables=decompiler.ssa.memory, assertions=[])

        main_function = [
            f for f in contract_functions if f.name == "__main__.test_symbolic_execution"
        ][0]
        test_cases = symbex._generate_test_cases(function=main_function)

        self.assertEqual(
            test_cases[-1],
            [
                ("v0_f", 6),
                ("v10_s", 19),
                ("v1_u", 21),
                ("v2_z", 26),
                ("v3_z2", 26),
                ("v4_i", 9),
                ("v5_n", 14),
                ("v6_g", 7),
                ("v7_l", 12),
                ("v8_a", 1),
                ("v9_b", 2),
            ],
        )

    def test_test_cases_generator_analyzer_2(self):
        """
        Test the test cases generator analyzer on test_symbolic_execution_3
        """
        disassembler = Disassembler(
            "./tests/json_files/cairo_0/cairo_test_symbolic_execution_3.json"
        )
        contract_functions = disassembler.functions
        decompiler = Decompiler(functions=contract_functions)
        decompiler.decompile_code(first_pass_only=True)

        symbex = SymbolicExecution(variables=decompiler.ssa.memory, assertions=[])

        main_function = [
            f for f in contract_functions if f.name == "__main__.test_symbolic_execution"
        ][0]
        test_cases = symbex._generate_test_cases(function=main_function)

        self.assertEqual(
            test_cases[1],
            [
                ("v0_f", 103),
                ("v10_s", 116),
                ("v1_u", 118),
                ("v2_z", 123),
                ("v3_z2", 123),
                ("v4_i", 106),
                ("v5_n", 111),
                ("v6_g", 104),
                ("v7_l", 109),
                ("v8_a", 98),
                ("v9_b", 99),
            ],
        )

    def test_symbolic_execution_1(self):
        """
        Test the symbolic execution _solve() function on cairo_test_symbolic_execution with equalities constraints
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/cairo_test_symbolic_execution.json")
        contract_functions = disassembler.functions
        decompiler = Decompiler(functions=contract_functions)
        decompiler.decompile_code(first_pass_only=True)

        symbex = SymbolicExecution(variables=decompiler.ssa.memory, assertions=[])

        symbex_function = [
            f for f in contract_functions if f.name == "__main__.test_symbolic_execution"
        ][0]
        symbex_constraints = ["v4==0", "v6==0"]
        symbex_variables = []
        symbex_solves = ["v0_x", "v1_y"]

        test_solve = symbex._solve(
            function=symbex_function,
            constraints=symbex_constraints,
            variables_values=symbex_variables,
            solves=symbex_solves,
        )

        self.assertEqual(test_solve, [("v0_x", 10), ("v1_y", 15)])

    def test_symbolic_execution_2(self):
        """
        Test the symbolic execution _solve() function on cairo_test_symbolic_execution with inequalities constraints
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/cairo_test_symbolic_execution.json")
        contract_functions = disassembler.functions
        decompiler = Decompiler(functions=contract_functions)
        decompiler.decompile_code(first_pass_only=True)

        symbex = SymbolicExecution(variables=decompiler.ssa.memory, assertions=[])

        symbex_function = [
            f for f in contract_functions if f.name == "__main__.test_symbolic_execution"
        ][0]
        symbex_constraints = ["v4!=0", "v6!=0"]
        symbex_variables = []
        symbex_solves = ["v0_x", "v1_y"]

        test_solve = symbex._solve(
            function=symbex_function,
            constraints=symbex_constraints,
            variables_values=symbex_variables,
            solves=symbex_solves,
        )

        self.assertEqual(test_solve, [("v0_x", 11), ("v1_y", 16)])

    def test_symbolic_execution_3(self):
        """
        Test the symbolic execution _solve() function on cairo_test_symbolic_execution with variables inequalities constraints
        """
        disassembler = Disassembler("./tests/json_files/cairo_0/cairo_test_symbolic_execution.json")
        contract_functions = disassembler.functions
        decompiler = Decompiler(functions=contract_functions)
        decompiler.decompile_code(first_pass_only=True)

        symbex = SymbolicExecution(variables=decompiler.ssa.memory, assertions=[])

        symbex_function = [
            f for f in contract_functions if f.name == "__main__.test_symbolic_execution"
        ][0]
        symbex_constraints = ["v4!=v6"]
        symbex_variables = []
        symbex_solves = ["v0_x", "v1_y"]

        test_solve = symbex._solve(
            function=symbex_function,
            constraints=symbex_constraints,
            variables_values=symbex_variables,
            solves=symbex_solves,
        )

        self.assertEqual(test_solve, [("v0_x", 1)])

    def test_symbolic_execution_4(self):
        """
        Test the symbolic execution _solve() function on cairo_test_symbolic_execution with variables replacements and equalities constraints
        """
        disassembler = Disassembler(
            "./tests/json_files/cairo_0/cairo_test_symbolic_execution_3.json"
        )
        contract_functions = disassembler.functions
        decompiler = Decompiler(functions=contract_functions)
        decompiler.decompile_code(first_pass_only=True)

        symbex = SymbolicExecution(variables=decompiler.ssa.memory, assertions=[])

        symbex_function = [
            f for f in contract_functions if f.name == "__main__.test_symbolic_execution"
        ][0]
        symbex_constraints = ["v13==0", "v14==0", "v15==0"]
        symbex_variables = ["v3_z2=26"]
        symbex_solves = ["v0_f", "v1_u", "v2_z", "v3_z2"]

        test_solve = symbex._solve(
            function=symbex_function,
            constraints=symbex_constraints,
            variables_values=symbex_variables,
            solves=symbex_solves,
        )

        self.assertEqual(test_solve, [("v0_f", 102), ("v1_u", 117), ("v2_z", 122), ("v3_z2", 26)])

    def test_symbolic_execution_5(self):
        """
        Test the symbolic execution _solve() function on cairo_test_symbolic_execution with a variable replacement and assertions
        """
        disassembler = Disassembler(
            "./tests/json_files/cairo_0/cairo_test_symbolic_execution_4.json"
        )
        contract_functions = disassembler.functions
        decompiler = Decompiler(functions=contract_functions)
        decompiler.decompile_code(first_pass_only=True)

        assertions = decompiler.assertions
        symbex = SymbolicExecution(variables=decompiler.ssa.memory, assertions=assertions)

        symbex_function = [
            f for f in contract_functions if f.name == "__main__.test_symbolic_execution"
        ][0]
        symbex_constraints = ["v4!=v6"]
        symbex_variables = []
        symbex_solves = ["v2", "v3", "v4", "v5", "v6", "v7", "v8", "v9"]

        test_solve = symbex._solve(
            function=symbex_function,
            constraints=symbex_constraints,
            variables_values=symbex_variables,
            solves=symbex_solves,
        )

        self.assertEqual(
            test_solve,
            [
                ("v2", 102),
                ("v3", 117),
                ("v4", 122),
                ("v5", 122),
                ("v6", 105),
                ("v7", 110),
                ("v8", 103),
                ("v9", 108),
            ],
        )


if __name__ == "__main__":
    unittest.main()
