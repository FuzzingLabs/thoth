import unittest
import glob
import os
import sys
from thoth.disassembler import Disassembler


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
        Check if the disassembler is working well
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
        Check if the disassembler is working well
        """
        with open("./tests/json_files/cairo_all_builtins.json", "r") as file:
            disassembler = Disassembler([file])
        analytics = disassembler.analytics()
        self.assertEqual(analytics["entry_point"], ["__main__.main"])
        self.assertEqual(analytics["functions"], "1")
        self.assertEqual(analytics["builtins"], "4")
        self.assertEqual(analytics["decorators"], [])
        self.assertEqual(analytics["call_nbr"], "0")


if __name__ == "__main__":
    unittest.main()
