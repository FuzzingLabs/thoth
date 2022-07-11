func a{}():
    a()
    ret
end

func b{}():
    c()
    ret
end

func c{}():
    b()
    ret
end

func main{}():
    [ap-1] = 5
    ret
end