func a{}(b : felt):
    if b == 4:
        ret
    else:
        a(b-1)
    end
    ret
end

func main{}():
    [ap-1] = 5

    if [ap-1] == 5:
        a(5)
    else:
        a(10)
    end
    ret
end