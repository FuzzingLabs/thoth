%lang starknet

func return_10() -> (res : felt):
    let res = 10
    return (res)
end

@view
func get_10{
    }() -> (
        value : felt
    ):
    let (value) = return_10()
    return (value)
end
