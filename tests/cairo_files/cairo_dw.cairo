from starkware.cairo.common.registers import get_label_location

// Returns a pointer to the values: [1, 22, 333, 4444].
func get_data() -> (data: felt*) {
    let (data_address) = get_label_location(data_start);
    return (data=cast(data_address, felt*));

    data_start:
    dw 1;
    dw 22;
    dw 333;
    dw 4444;
}

func main() {
    let (data) = get_data();
    tempvar value = data[2];
    assert value = 333;
    return ();
}