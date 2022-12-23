func a{}():
    if 1 == 2:
        a()
    else:
        b()
    end
    ret
end

func b{}():
    if 1 == 2:
        b()
    else:
        c()
    end
    ret
end

func c{}():
    if 1 == 2:
        c()
    else:
        d()
    end
    ret
end

func d{}():
    if 1 == 2:
        d()
    else:
        a()
    end
    ret
end

func main{}():
    if 1 == 2:
        a()
    else:
        b()
    end
    ret
end