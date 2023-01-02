func a{}() -> (b : felt):
    return (5)
end

func main{}():
    a()
    if [ap-1] == 5:
        a()
    end

    if [ap-1] == 0:
        [ap] = 1; ap++
        [ap] = 1
    end
    ret
end