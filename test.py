import unittest
from disassembler import Disassembler

class TestDisassembler(unittest.TestCase):
    def test_cairo_return(self):
        file = open("./tests/json_files/cairo_return.json", "r")
        disassembler = Disassembler([file])
        analytics = disassembler.analytics()
        self.assertEqual(analytics["entry_point"], "__main__.main")
        self.assertEqual(analytics["functions"], "2")
        self.assertEqual(analytics["builtins"], "0")
        self.assertEqual(analytics["decorators"], [])
        self.assertEqual(analytics["call_nbr"], "2")

        
    def test_FILENAME(self):
        """
            Open the file
            create the disassembler object
            get the analytics
            compare
        """
        file = open("./tests/json_files/cairo_return.json", "r")
        disassembler = Disassembler([file])
        analytics = disassembler.analytics()


if __name__ == '__main__':
    unittest.main()