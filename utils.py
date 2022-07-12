operator = {"ADD" : "+", "MUL" : "*"}
prime = (2**251) + (17 * (2**192)) + 1

def fPrint(data, end="\n"):
    spaces = " " * 15
    print(data + spaces[len(data):], end=end)
