%lang starknet
%builtins ecdsa

from starkware.cairo.common.signature import verify_ecdsa_signature
from starkware.cairo.common.cairo_builtins import SignatureBuiltin

@view
func check_signature{ecdsa_ptr: SignatureBuiltin*}(
        message, public_key, sig_r, sig_s) -> ():
    verify_ecdsa_signature(message, public_key, sig_r, sig_s)
    return ()
end