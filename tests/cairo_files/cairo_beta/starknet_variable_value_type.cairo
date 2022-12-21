%lang starknet

from starkware.cairo.common.dict import DictAccess, dict_new
from starkware.cairo.common.cairo_builtins import HashBuiltin, SignatureBuiltin



struct MyStruct:
    member a : felt
    member b : felt
end

struct AnotherStruct:
    member a : felt
    member b : MyStruct
    member c : felt*
    member d : MyStruct*
    member e : felt
end

# storage_var is a primitive type for StarkNet contract
# When a contract is deployed, all its storage cells are initialized to zero.
@storage_var
func a_storage_var(mystruct : MyStruct) -> (res : felt):
end
# To use this variable, we will use the balance.read() and balance.write() functions which the @storage_var decorator automatically creates. 

# Arguments of storage variables must be felts-only type (cannot contain pointers)
@storage_var
func another_storage_var(mystruct : MyStruct, a_felt : felt) -> (
    res : felt
):
end


func a{}(param1 : MyStruct, param2 : MyStruct*):
    ret
end

func b{pedersen_ptr : HashBuiltin*, ecdsa_ptr : SignatureBuiltin*}():
    ret
end

func c{pedersen_ptr : HashBuiltin*, ecdsa_ptr : SignatureBuiltin*}(param1 : MyStruct, param2 : MyStruct*):
    ret
end


func main{}(output_ptr : felt*):
    # Primitive type : field element (felt)
    # felt* is an array of felt

    let (dict : DictAccess*) = dict_new()

    # syscall_ptr -> a primitive unique to StarkNet contracts which allows the code to invoke system calls
    ret
end