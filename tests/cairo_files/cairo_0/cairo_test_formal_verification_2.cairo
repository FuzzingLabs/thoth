from starkware.cairo.common.math_cmp import is_le_felt

func test_formal_verification{range_check_ptr}(amount: felt) -> felt {
    let balance = 1000;
    
    let is_le = is_le_felt(balance, amount);
    if (amount == 42) {
        let new_balance = - 1;
        return(new_balance);
    }
    if (is_le == 0) {
        let new_balance = balance - amount;
        return(new_balance);
    } 
    return(balance);
}

func main() {
    return();
}