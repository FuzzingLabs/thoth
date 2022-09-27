import unittest
import glob
import os
import sys
from thoth.app.disassembler.disassembler import Disassembler


class TestDisassembler(unittest.TestCase):
    """
    Testing class
    """

    # def test_all_files_tested(self):
    #     """
    #     Check that all the json files have been analyzed manually and added in tests
    #     """
    #    all_test = glob.glob("./tests/json_files/*")
    #    number_of_tests = len(
    #        [method for method in dir(TestDisassembler) if method.startswith("test_")]
    #   )
    #    self.assertEqual(len(all_test), number_of_tests - 1)

    def test_no_file_should_crash(self):
        """test_no_file_should_crash"""
        all_test = glob.glob("./tests/json_files/*")
        crash = 0
        f = open("/dev/null", "w")
        save_stdout = sys.stdout
        sys.stdout = f
        for test in all_test:
            try:
                with open(test, "r") as file:
                    disassembler = Disassembler([file])
                    disassembler.print_disassembly()
                    filename = os.path.basename(file.name).split(".")[0]
                    format = "pdf"
                    disassembler.print_call_flow_graph(filename=filename, format=format, view=False)
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
        with open("./tests/json_files/cairo_return.json", "r") as file:
            disassembler = Disassembler([file])
        analytics = disassembler.analytics()
        self.assertEqual(analytics["entry_point"], ["__main__.main"])
        self.assertEqual(analytics["functions"], "2")
        self.assertEqual(analytics["builtins"], "0")
        self.assertEqual(analytics["decorators"], [])
        self.assertEqual(analytics["call_nbr"], "2")

    def test_cairo_all_builtins(self):
        """
        test_cairo_all_builtins
        """
        with open("./tests/json_files/cairo_all_builtins.json", "r") as file:
            disassembler = Disassembler([file])
        analytics = disassembler.analytics()
        self.assertEqual(analytics["entry_point"], ["__main__.main"])
        self.assertEqual(analytics["functions"], "1")
        self.assertEqual(analytics["builtins"], "4")
        self.assertEqual(analytics["decorators"], [])
        self.assertEqual(analytics["call_nbr"], "0")

    def test_cairo_direct_and_indirect_recursion(self):
        """
        test_cairo_direct_and_indirect_recursion
        """
        with open("./tests/json_files/cairo_direct_and_indirect_recursion.json", "r") as file:
            disassembler = Disassembler([file])
        analytics = disassembler.analytics()
        self.assertEqual(analytics["entry_point"], ["__main__.main"])
        self.assertEqual(analytics["functions"], "5")
        self.assertEqual(analytics["builtins"], "0")
        self.assertEqual(analytics["decorators"], [])
        self.assertEqual(analytics["call_nbr"], "10")

    def test_cairo_struct(self):
        """
        test_cairo_struct
        """
        with open("./tests/json_files/cairo_struct.json", "r") as file:
            disassembler = Disassembler([file])
        analytics = disassembler.analytics()
        self.assertEqual(analytics["entry_point"], ["__main__.main"])
        self.assertEqual(analytics["functions"], "1")
        self.assertEqual(analytics["builtins"], "0")
        self.assertEqual(analytics["decorators"], [])
        self.assertEqual(analytics["call_nbr"], "0")
        self.assertEqual(analytics["structs"], 4)

    def test_cairo_puzzle(self):
        """test_cairo_puzzle"""
        with open("./tests/json_files/cairo_puzzle.json", "r") as file:
            disassembler = Disassembler([file])
        analytics = disassembler.analytics()
        self.assertEqual(analytics["entry_point"], ["__main__.main"])
        self.assertEqual(analytics["functions"], "18")
        self.assertEqual(analytics["builtins"], "2")
        self.assertEqual(analytics["decorators"], ["known_ap_change", "known_ap_change"])
        self.assertEqual(analytics["call_nbr"], "30")
        self.assertEqual(analytics["structs"], 59)

    def test_starknet_decorators3(self):
        """
        test_starknet_decorators3
        """
        with open("./tests/json_files/starknet_decorators3.json", "r") as file:
            disassembler = Disassembler([file])
        analytics = disassembler.analytics()
        self.assertEqual(
            analytics["entry_point"], ["__wrappers__.increase_balance", "__wrappers__.get_balance"]
        )
        self.assertEqual(analytics["functions"], "15")
        self.assertEqual(analytics["builtins"], "2")
        self.assertEqual(
            analytics["decorators"],
            ["known_ap_change", "known_ap_change", "external", "external", "view", "view"],
        )
        self.assertEqual(analytics["call_nbr"], "18")
        self.assertEqual(analytics["structs"], 88)

    def test_starknet_l1_default(self):
        """
        test_starknet_l1_default
        """
        with open("./tests/json_files/starknet_l1_default.json", "r") as file:
            disassembler = Disassembler([file])
        analytics = disassembler.analytics()
        self.assertEqual(
            analytics["entry_point"],
            [
                "__wrappers__.constructor",
                "__wrappers__.__default__",
                "__wrappers__.__l1_default__",
            ],
        )
        self.assertEqual(analytics["functions"], "13")
        self.assertEqual(analytics["builtins"], "3")
        self.assertEqual(
            analytics["decorators"],
            [
                "external",
                "external",
                "external",
                "raw_input",
                "raw_output",
                "external",
                "raw_input",
                "raw_output",
                "l1_handler",
                "raw_input",
                "l1_handler",
                "raw_input",
            ],
        )
        self.assertEqual(analytics["call_nbr"], "12")
        self.assertEqual(analytics["structs"], 79)

    def test_starknet_get_code_l2_dai_bridge(self):
        """test_starknet_get_code_l2_dai_bridge"""
        with open("./tests/json_files/starknet_get_code_l2_dai_bridge.json", "r") as file:
            disassembler = Disassembler([file])
        analytics = disassembler.analytics()
        self.assertEqual(analytics["entry_point"], ["unknown_function"])
        self.assertEqual(analytics["functions"], "1")
        self.assertEqual(analytics["builtins"], "0")
        self.assertEqual(analytics["decorators"], [])
        self.assertEqual(analytics["call_nbr"], "135")
        self.assertEqual(analytics["structs"], 0)


if __name__ == "__main__":
    unittest.main()
