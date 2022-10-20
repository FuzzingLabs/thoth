import glob
import os
import sys
import unittest

import thoth.app.analyzer as analyzer
from thoth.app.analyzer import all_analyzers
from thoth.app.disassembler.disassembler import Disassembler


class TestDisassembler(unittest.TestCase):
    """
    Testing class
    """

    def test_disassembler_no_file_should_crash(self):
        """
        Test the disassembler on all files
        """
        all_test = glob.glob("./tests/json_files/*")
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
        disassembler = Disassembler("./tests/json_files/cairo_amm.json")
        crash = 0

        for a in all_analyzers:
            try:
                a(disassembler)._detect()
            except:
                crash += 1
        self.assertEqual(crash, 0)

    def test_cairo_return_functions_analyzer(self):
        """
        Test the functions analyzer on cairo_return
        """
        disassembler = Disassembler("./tests/json_files/cairo_return.json")
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
        disassembler = Disassembler("./tests/json_files/cairo_all_builtins.json")
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
        disassembler = Disassembler("./tests/json_files/cairo_all_builtins.json")
        functions_analyzer = analyzer.FunctionsAnalyzer(disassembler, color=False)
        functions_analyzer._detect()

        self.assertEqual(functions_analyzer.result[0], "main (entry point)")

    def test_cairo_direct_and_indirect_recursion_statistics_analyzer(self):
        """
        Test the statistics analyzer on cairo_direct_and_indirect_recursion
        """
        disassembler = Disassembler("./tests/json_files/cairo_direct_and_indirect_recursion.json")
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
        disassembler = Disassembler("./tests/json_files/cairo_direct_and_indirect_recursion.json")
        functions_analyzer = analyzer.FunctionsAnalyzer(disassembler, color=False)
        functions_analyzer._detect()

        self.assertEqual(functions_analyzer.result[0], "a")
        self.assertEqual(functions_analyzer.result[1], "b")
        self.assertEqual(functions_analyzer.result[2], "c")
        self.assertEqual(functions_analyzer.result[3], "d")
        self.assertEqual(functions_analyzer.result[4], "main (entry point)")

    def test_cairo_struct_statistics_analyzer(self):
        """
        Test the statistics analyzer on cairo_struct
        """
        disassembler = Disassembler("./tests/json_files/cairo_struct.json")
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
        disassembler = Disassembler("./tests/json_files/cairo_puzzle.json")
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
        disassembler = Disassembler("./tests/json_files/starknet_decorators3.json")
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
        disassembler = Disassembler("./tests/json_files/starknet_decorators3.json")
        functions_analyzer = analyzer.FunctionsAnalyzer(disassembler, color=False)
        functions_analyzer._detect()

        self.assertEqual(functions_analyzer.result[0], "__main__.balance.addr")
        self.assertEqual(functions_analyzer.result[1], "__main__.balance.read")
        self.assertEqual(functions_analyzer.result[2], "__main__.balance.write")
        self.assertEqual(
            functions_analyzer.result[3], "increase_balance\n\t- decorators : external"
        )
        self.assertEqual(
            functions_analyzer.result[4],
            "__wrappers__.increase_balance (entry point)\n\t- decorators : external",
        )
        self.assertEqual(functions_analyzer.result[5], "get_balance\n\t- decorators : view")
        self.assertEqual(functions_analyzer.result[6], "__wrappers__.get_balance_encode_return")
        self.assertEqual(
            functions_analyzer.result[7],
            "__wrappers__.get_balance (entry point)\n\t- decorators : view",
        )

    def test_starknet_l1_default_statistics_analyzer(self):
        """
        Test the statistics analyzer on starknet_l1_default
        """
        disassembler = Disassembler("./tests/json_files/starknet_l1_default.json")
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
        disassembler = Disassembler("./tests/json_files/starknet_l1_default.json")
        functions_analyzer = analyzer.FunctionsAnalyzer(disassembler, color=False)
        functions_analyzer._detect()

        self.assertEqual(functions_analyzer.result[0], "__main__.impl_address.addr")
        self.assertEqual(functions_analyzer.result[1], "__main__.impl_address.read")
        self.assertEqual(functions_analyzer.result[2], "__main__.impl_address.write")
        self.assertEqual(functions_analyzer.result[3], "constructor\n\t- decorators : external")
        self.assertEqual(
            functions_analyzer.result[4],
            "__wrappers__.constructor (entry point)\n\t- decorators : external",
        )
        self.assertEqual(
            functions_analyzer.result[5],
            "__default__\n\t- decorators : external, raw_input, raw_output",
        )
        self.assertEqual(
            functions_analyzer.result[6],
            "__wrappers__.__default__ (entry point)\n\t- decorators : external, raw_input, raw_output",
        )
        self.assertEqual(
            functions_analyzer.result[7],
            "__l1_default__ <- L1\n\t- decorators : l1_handler, raw_input",
        )
        self.assertEqual(
            functions_analyzer.result[8],
            "__wrappers__.__l1_default__ <- L1 (entry point)\n\t- decorators : l1_handler, raw_input",
        )

    def test_starknet_get_code_l2_dai_bridge_statistics_analyzer(self):
        """
        Test the statistics analyzer on starknet_get_code_l2_dai_bridge
        """
        disassembler = Disassembler("./tests/json_files/starknet_get_code_l2_dai_bridge.json")
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
        disassembler = Disassembler("./tests/json_files/starknet_send_message_to_l1.json")
        functions_analyzer = analyzer.FunctionsAnalyzer(disassembler, color=False)
        functions_analyzer._detect()

        self.assertEqual(functions_analyzer.result[0], "generate -> L1\n\t- decorators : external")
        self.assertEqual(
            functions_analyzer.result[1],
            "__wrappers__.generate (entry point)\n\t- decorators : external",
        )

    def test_starknet_erc20_erc20_analyzer(self):
        """
        Test the ERC20 analyzer
        """
        disassembler = Disassembler("./tests/json_files/starknet_erc20.json")
        functions_analyzer = analyzer.ERC20Analyzer(disassembler, color=False)
        functions_analyzer._detect()

        self.assertEqual(functions_analyzer.detected, True)

    def test_starknet_erc721_erc721_analyzer(self):
        """
        Test the ERC721 analyzer
        """
        disassembler = Disassembler("./tests/json_files/starknet_erc721.json")
        functions_analyzer = analyzer.ERC721Analyzer(disassembler, color=False)
        functions_analyzer._detect()

        self.assertEqual(functions_analyzer.detected, True)

    def test_starknet_integer_overflow_integer_overflow_detector(self):
        """
        Test the Integer Overflow Detector
        """
        disassembler = Disassembler("./tests/json_files/cairo_integer_overflow.json")
        integer_overflow_detector = analyzer.IntegerOverflowDetector(disassembler, color=False)
        integer_overflow_detector._detect()

        self.assertEqual(integer_overflow_detector.detected, True)

    def test_starknet_get_code_l2_dai_bridge_functions_naming_analyzer(self):
        """
        Test the variable naming analyzer on starknet_get_code_l2_dai_bridge
        """
        disassembler = Disassembler(
            "./tests/json_files/starknet_get_full_contract_l2_dai_bridge.json"
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
        disassembler = Disassembler("./tests/json_files/starknet_erc20_mintable.json")
        statistics_analyzer = analyzer.VariableNamingAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(
            statistics_analyzer.result[0],
            "newOwner argument name (transferOwnership function) needs to be in snake case",
        )


if __name__ == "__main__":
    unittest.main()
