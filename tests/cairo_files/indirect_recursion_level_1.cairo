func a{}():
    b()
    ret
end

func b{}():
    a()
    ret
end

func main{}():
    a()
    ret
end