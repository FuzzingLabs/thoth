func myfunc(a, b, c):
    let d = c + a + b
    ret
end

func myfuncbis(a,b):
    let c = a + b
    let d = c + 5
    ret
end

func main{}():
    let a = 1
    let b = 2
    let c = 3
    myfunc(b, a, c)
    myfuncbis(c, a)
    ret
end
