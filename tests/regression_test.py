from os import listdir
from os.path import isfile, join
from disassembler import *

success = True

# get all files
files = [f for f in listdir("tests/") if isfile(join("tests/", f))]

# split in lists
json_files = [f for f in files if ".json" in f] # test files for the disassembler


for f in json_files:
	# disassembling and testing results
	try:
		assert disassemble(f) == open(f.split(".")[0] + ".txt",'r').read()
	except Exception as e:
		success = False
		# TODO : don't print all the exception
		print(e)


print("\nSuccess\n" if success else "\nNot a success\n")