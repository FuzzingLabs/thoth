func main{}():
    
    let MY_STR = 'Hello World!'

    %{
        print(ids.MY_STR)
        print("It was the representation of 'Hello World!' in Cairo")
    %}

    return ()
end