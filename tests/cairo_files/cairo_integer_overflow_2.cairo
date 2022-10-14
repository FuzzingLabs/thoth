%builtins output

// Import the serialize_word() function.
from starkware.cairo.common.serialize import serialize_word

func vulnerable_function{output_ptr: felt*}(integer: felt) {
    tempvar x = 1809251394333065606848661391547535052811553607665798349986546028067936010240;
    tempvar z = integer;
    tempvar y = x + z;
    serialize_word(y);
    return();
}

func main{output_ptr: felt*}() {
    vulnerable_function(1);
    return ();
}