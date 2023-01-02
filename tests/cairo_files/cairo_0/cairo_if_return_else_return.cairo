func a{}() -> (b : felt):
    [ap-1] = 1; ap ++

    if [ap-1] == 1:
        return(1)
    else:
        return(2)
    end
end
    

func main{}():
    a()
    ret
end