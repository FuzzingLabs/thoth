func a{}():
    b()
    ret
end

func b{}():
    c()
    ret
end

func c{}():
    a()
    ret
end

func main{}():
    a()
    ret
end