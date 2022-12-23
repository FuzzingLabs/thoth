import glob
import sys
import unittest
from sierra import config

from sierra.parser.parser import SierraParser


class TestDisassembler(unittest.TestCase):
    """
    Testing class
    """

    def test_disassembler_no_file_should_crash(self):
        """
        Test the disassembler on all files
        """
        all_test = glob.glob("/home/rog3r/Bureau/thoth/tests/sierra_files/*")
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


if __name__ == "__main__":
    unittest.main()
