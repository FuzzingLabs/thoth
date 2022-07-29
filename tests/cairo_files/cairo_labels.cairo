func my_function() -> (result):
    jmp case_false

    case_false:
    return (result=0)

    jmp case_true

    case_true:
    return (result=1)
end