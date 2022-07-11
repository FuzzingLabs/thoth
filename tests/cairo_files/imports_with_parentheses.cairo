%builtins output pedersen range_check ecdsa bitwise

# there is from foo import *

from starkware.cairo.common.alloc import alloc
from starkware.cairo.common.bitwise import (
    bitwise_operations,
    bitwise_and,
    bitwise_xor,
    bitwise_or,
    bitwise_not,
    )
from starkware.cairo.common.bool import (
    FALSE,
    TRUE,
    )
from starkware.cairo.common.cairo_builtins import (
    HashBuiltin,
    SignatureBuiltin,
    BitwiseBuiltin,
    EcOpBuiltin,
    )
from starkware.cairo.common.default_dict import (
    default_dict_new,
    default_dict_finalize, 
    default_dict_finalize_inner,
    )
from starkware.cairo.common.dict import (
    dict_new,
    dict_read,
    dict_write,
    dict_update,
    dict_squash,
    )
from starkware.cairo.common.dict_access import DictAccess
from starkware.cairo.common.ec_point import EcPoint
from starkware.cairo.common.find_element import (
    find_element,
    search_sorted_lower,
    search_sorted,
    )
from starkware.cairo.common.hash import hash2
from starkware.cairo.common.hash_chain import hash_chain
from starkware.cairo.common.hash_state import (
    HashState,
    hash_init,
    hash_update_single,
    hash_finalize,
    hash_update_inner,
    )
from starkware.cairo.common.invoke import (
    invoke,
    invoke_prepare_args,
    )
from starkware.cairo.common.keccak import (
    unsafe_keccak,
    KeccakState,
    unsafe_keccak_init,
    unsafe_keccak_add_felt,
    unsafe_keccak_add_uint256,
    unsafe_keccak_add_felts,
    unsafe_keccak_finalize,
    keccak_felts,
    truncated_keccak2,
    )
from starkware.cairo.common.math import (
    assert_not_zero,
    assert_not_equal,
    assert_nn,
    assert_le,
    assert_lt,
    assert_nn_le,
    assert_250_bit,
    split_felt,
    assert_le_felt,
    assert_lt_felt,
    abs_value,
    sign,
    unsigned_div_rem,
    signed_div_rem,
    split_int,
    sqrt,
    horner_eval,
    )
from starkware.cairo.common.math_cmp import (
    RC_BOUND,
    is_nn,
    is_le,
    is_nn_le,
    is_in_range,
    is_le_felt,
    )
from starkware.cairo.common.memcpy import memcpy
from starkware.cairo.common.memset import memset
from starkware.cairo.common.merkle_multi_update import (
    merkle_multi_update,
    merkle_multi_update_inner,
    )
from starkware.cairo.common.merkle_update import merkle_update
from starkware.cairo.common.patricia import (
    MAX_LENGTH,
    ParticiaGlobals,
    NodeEdge,
    PatriciaUpdateConstants,
    open_edge,
    traverse_empty,
    traverse_edge,
    traverse_binary_or_leaf,
    traverse_node,
    traverse_non_empty,
    compute_pow2_array,
    patricia_update,
    patricia_update_constants_new,
    patricia_update_using_update_constants,
    )
from starkware.cairo.common.pow import pow
from starkware.cairo.common.registers import get_label_location
from starkware.cairo.common.segments import relocate_segment
from starkware.cairo.common.serialize import (
    serialize_word,
    array_rfold,
    serialize_array,
    )
from starkware.cairo.common.set import (
    SET_ADD_RANGE_CHECK_USAGE_ON_DUPLICATE,
    SET_ADD_RANGE_CHECK_USAGE_ON_NO_DUPLICATE,
    set_add,
    )
from starkware.cairo.common.signature import verify_ecdsa_signature
from starkware.cairo.common.small_merkle_tree import small_merkle_tree_update
from starkware.cairo.common.squash_dict import (
    squash_dict,
    squash_dict_inner,
    )
from starkware.cairo.common.uint256 import (
    Uint256,
    SHIFT,
    ALL_ONES,
    HALF_SHIFT,
    uint256_check,
    uint256_add, split_64,
    uint256_mul,
    uint256_sqrt,
    uint256_lt,
    uint256_signed_lt,
    uint256_le,
    uint256_signed_le,
    uint256_signed_nn,
    uint256_signed_nn_le,
    uint256_neg,
    uint256_cond_neg,
    uint256_signed_div_rem,
    uint256_sub,
    uint256_eq,
    uint256_xor,
    uint256_and,
    uint256_or,
    uint256_pow2,
    uint256_shl,
    uint256_shr,
    )
from starkware.cairo.common.usort import (
    usort,
    verify_usort,
    verify_multiplicity,
    )

func main{output_ptr : felt*,
    pedersen_ptr : HashBuiltin*,
    range_check_ptr,
    ecdsa_ptr : SignatureBuiltin*,
    bitwise_ptr : BitwiseBuiltin*,
    }():

    ret
end