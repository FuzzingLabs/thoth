from starkware.cairo.common.registers import get_label_location

// Returns a pointer to the values: [1, 22, 333, 4444].
func get_data() -> (data: felt*) {
    let (data_address) = get_label_location(data_start);
    return (data=cast(data_address, felt*));

    data_start:
        dw 340282366920938463463374607431768211456;
        dw 1329227995784915872903807060280344576;
        dw 5192296858534827628530496329220096;
        dw 20282409603651670423947251286016;
        dw 79228162514264337593543950336;
        dw 309485009821345068724781056;
        dw 1208925819614629174706176;
        dw 4722366482869645213696;
        dw 18446744073709551616;
        dw 72057594037927936;
        dw 281474976710656;
        dw 1099511627776;
        dw 4294967296;
        dw 16777216;
        dw 65536;
        dw 256;
        dw 1;
}

func main() {
    let (data) = get_data();
    tempvar value = data[2];
    assert value = 333;
    return ();
}