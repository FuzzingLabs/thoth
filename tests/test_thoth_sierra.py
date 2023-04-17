import glob
import sys
import unittest

from sierra import config
from sierra.parser.parser import SierraParser
from sierra.symbex.symbex import SierraSymbolicExecution


class TestSierra(unittest.TestCase):
    """
    Testing class
    """

    def test_parser_no_file_should_crash(self):
        """
        Test the parser on all files
        """
        all_test = glob.glob("./tests/sierra_files/*")
        crash = 0
        f = open("/dev/null", "w")
        save_stdout = sys.stdout
        sys.stdout = f
        for test in all_test:
            try:
                parser = SierraParser(config.SIERRA_LARK_PARSER_PATH)
                parser.parse(test)
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

    def test_symbolic_execution(self):
        """
        Test the symbolic execution
        """
        parser = SierraParser(config.SIERRA_LARK_PARSER_PATH)
        parser.parse("./tests/sierra_files/symbolic_execution_test.sierra")

        function = [
            f for f in parser.functions if f.id == "symbolic::symbolic::symbolic_execution_test"
        ][0]
        solves = ["v0", "v1", "v2", "v3"]
        constraints = ["v5==0", "v8==0", "v11==0", "v14==0"]

        symbolic_execution = SierraSymbolicExecution(function=function)
        solve = symbolic_execution.solve(
            constraints=constraints, solves=solves, variables_values=[]
        )

        self.assertEqual(solve, [("v0", 102), ("v1", 117), ("v2", 122), ("v3", 122)])


if __name__ == "__main__":
    unittest.main()
