func a{}():
    [ap] = 5; ap ++

    if [ap-1] == 2:
        [ap] = [ap-1] + 3; ap ++
    else:
        [ap] = 10; ap ++
    end
    ret
end
    
func b{}():
    [ap] = 5; ap ++
    ret
end

func main{}():
    [ap-1] = 2
    
    if [ap-1] == 5:
        a()
    else:
        b()
    end

    ret
end