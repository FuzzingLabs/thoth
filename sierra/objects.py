class SierraObject:

    current_object_id = 0

    """
    Base object from which all Sierra objects are inherited from
    """

    def __init__(self) -> None:
        self.id = SierraObject.current_object_id
        SierraObject.current_object_id += 1


class SierraType(SierraObject):
    """
    Sierra Type class
    """

    def __init__(self, name: str) -> None:
        super(SierraType, self).__init__()
        self.name = name


class SierraLibFunc(SierraObject):
    """
    Sierra LibFunc class
    """

    def __init__(self, name: str) -> None:
        super(SierraLibFunc, self).__init__()
        self.name = name


class SierraStatement(SierraObject):
    """
    Sierra Statement class
    """

    def __init__(self) -> None:
        super(SierraType, self).__init__()


class SierraFunction(SierraObject):
    """
    Sierra Function class
    """

    def __init__(self) -> None:
        super(SierraType, self).__init__()
