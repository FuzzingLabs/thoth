class colors:
    @classmethod
    def __init__(cls, color: bool = True) -> None:
        cls.HEADER = "\033[95m" if color else ""
        cls.BLUE = "\033[94m" if color else ""
        cls.CYAN = "\033[96m" if color else ""
        cls.GREEN = "\033[92m" if color else ""
        cls.YELLOW = "\033[93m" if color else ""
        cls.MAGENTA = "\033[35m" if color else ""
        cls.WARNING = "\033[93m" if color else ""
        cls.RED = "\033[91m" if color else ""
        cls.ENDC = "\033[0m" if color else ""
        cls.BOLD = "\033[1m" if color else ""
        cls.UNDERLINE = "\033[4m" if color else ""
