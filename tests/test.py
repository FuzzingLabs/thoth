import unittest
import glob

from disassembler import Disassembler


class TestDisassembler(unittest.TestCase):
    """
    Testing class
    """

    def test_all_files_tested(self):
        """
        Check that all the json files have been analyzed manually and added in tests
        """
        all_test = glob.glob("./tests/json_files/*")
        number_of_tests = len(
            [method for method in dir(TestDisassembler) if method.startswith("test_")]
        )
        self.assertEqual(len(all_test), number_of_tests - 1)

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


if __name__ == "__main__":
    unittest.main()
