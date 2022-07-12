%lang starknet

@contract_interface
namespace IBalanceContract:
    func increase_balance(amount : felt):
    end

    func get_balance() -> (res : felt):
    end
end