from os import listdir
import sys
import subprocess

class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

test_files = [f for f in listdir("tests/ref_files")]
success = 0
fail = 0
for file in test_files:
	test_name = file.split(".")[0]
	rc = subprocess.call("tests/json_to_txt_tests.sh", stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
	data_tests = open("tests/test_files/" + test_name + ".txt", 'r').read()
	data_ref = open("tests/ref_files/" + test_name + ".txt", 'r').read()
	if (data_tests == data_ref):
		print (f"TEST - {test_name} - " + bcolors.OKGREEN + "SUCCESSED" + bcolors.ENDC)
		success += 1
	else:
		print (f"TEST - {test_name} - " + bcolors.FAIL + "FAILED" + bcolors.ENDC)
		fail += 1
print(f"TOTAL TESTS : {len(test_files)} -- Succes : " + bcolors.OKGREEN + f"{success}" + bcolors.ENDC + " -- Fail : " + bcolors.FAIL + f"{fail}" + bcolors.ENDC)