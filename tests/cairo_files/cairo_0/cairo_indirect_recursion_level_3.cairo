func a{}():
    b()
    ret
end

func b{}():
    c()
    ret
end

func c{}():
    d()
    ret
end

func d{}():
    a()
    ret
end

func main{}():
    a()
    ret
end