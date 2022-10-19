import glob
import os
import sys
import unittest
import thoth.app.analyzer as analyzer
from thoth.app.disassembler.disassembler import Disassembler


class TestDisassembler(unittest.TestCase):
    """
    Testing class
    """

    def test_no_file_should_crash(self):
        """test_no_file_should_crash"""
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

    def test_cairo_return(self):
        """
        test_cairo_return
        """
        disassembler = Disassembler("./tests/json_files/cairo_return.json")
        statistics_analyzer = analyzer.StatisticsAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(statistics_analyzer.result[0], "functions : 2")
        self.assertEqual(statistics_analyzer.result[1], "builtins : 0")
        self.assertEqual(statistics_analyzer.result[2], "structs : 6")
        self.assertEqual(statistics_analyzer.result[3], "calls : 2")

    def test_cairo_all_builtins(self):
        """
        test_cairo_all_builtins
        """
        disassembler = Disassembler("./tests/json_files/cairo_all_builtins.json")
        statistics_analyzer = analyzer.StatisticsAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(statistics_analyzer.result[0], "functions : 1")
        self.assertEqual(statistics_analyzer.result[1], "builtins : 4")
        self.assertEqual(statistics_analyzer.result[2], "structs : 8")
        self.assertEqual(statistics_analyzer.result[3], "calls : 0")

    def test_cairo_direct_and_indirect_recursion(self):
        """
        test_cairo_direct_and_indirect_recursion
        """
        disassembler = Disassembler("./tests/json_files/cairo_direct_and_indirect_recursion.json")
        statistics_analyzer = analyzer.StatisticsAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(statistics_analyzer.result[0], "functions : 5")
        self.assertEqual(statistics_analyzer.result[1], "builtins : 0")
        self.assertEqual(statistics_analyzer.result[2], "structs : 15")
        self.assertEqual(statistics_analyzer.result[3], "calls : 10")

    def test_cairo_struct(self):
        """
        test_cairo_struct
        """
        disassembler = Disassembler("./tests/json_files/cairo_struct.json")
        statistics_analyzer = analyzer.StatisticsAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(statistics_analyzer.result[0], "functions : 1")
        self.assertEqual(statistics_analyzer.result[1], "builtins : 0")
        self.assertEqual(statistics_analyzer.result[2], "structs : 4")
        self.assertEqual(statistics_analyzer.result[3], "calls : 0")

    def test_cairo_puzzle(self):
        """
        test_cairo_puzzle
        """
        disassembler = Disassembler("./tests/json_files/cairo_puzzle.json")
        statistics_analyzer = analyzer.StatisticsAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(statistics_analyzer.result[0], "functions : 18")
        self.assertEqual(statistics_analyzer.result[1], "builtins : 2")
        self.assertEqual(statistics_analyzer.result[2], "structs : 59")
        self.assertEqual(statistics_analyzer.result[3], "calls : 30")

    def test_starknet_decorators3(self):
        """
        test_starknet_decorators3
        """
        disassembler = Disassembler("./tests/json_files/starknet_decorators3.json")
        statistics_analyzer = analyzer.StatisticsAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(statistics_analyzer.result[0], "functions : 15")
        self.assertEqual(statistics_analyzer.result[1], "builtins : 2")
        self.assertEqual(statistics_analyzer.result[2], "structs : 88")
        self.assertEqual(statistics_analyzer.result[3], "calls : 18")

    def test_starknet_l1_default(self):
        """
        test_starknet_l1_default
        """
        disassembler = Disassembler("./tests/json_files/starknet_l1_default.json")
        statistics_analyzer = analyzer.StatisticsAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(statistics_analyzer.result[0], "functions : 13")
        self.assertEqual(statistics_analyzer.result[1], "builtins : 3")
        self.assertEqual(statistics_analyzer.result[2], "structs : 79")
        self.assertEqual(statistics_analyzer.result[3], "calls : 12")

    def test_starknet_get_code_l2_dai_bridge(self):
        """
        test_starknet_get_code_l2_dai_bridge
        """
        disassembler = Disassembler("./tests/json_files/starknet_get_code_l2_dai_bridge.json")
        statistics_analyzer = analyzer.StatisticsAnalyzer(disassembler)
        statistics_analyzer._detect()

        self.assertEqual(statistics_analyzer.result[0], "functions : 1")
        self.assertEqual(statistics_analyzer.result[1], "builtins : 0")
        self.assertEqual(statistics_analyzer.result[2], "structs : 0")
        self.assertEqual(statistics_analyzer.result[3], "calls : 135")


if __name__ == "__main__":
    unittest.main()
