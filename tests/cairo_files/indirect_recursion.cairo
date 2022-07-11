func a{}(b : felt):
    if b == 3:
        ret
    else:
        c(b-1)
    end
    ret
end

func c{}(b : felt):
    a(b-1)
    ret
end

func main{}():
    [ap-1] = 5

    if [ap-1] == 5:
        a(5)
    else:
        c(8)
    end
    ret
end