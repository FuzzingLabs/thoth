use integer::u8_is_zero;
use integer::u8_safe_divmod;
use integer::u8_to_felt252;
use integer::u8_wide_mul;
use integer::u16_is_zero;
use integer::u16_safe_divmod;
use integer::u16_to_felt252;
use integer::u16_wide_mul;
use integer::u32_is_zero;
use integer::u32_safe_divmod;
use integer::u32_to_felt252;
use integer::u32_wide_mul;
use integer::u64_is_zero;
use integer::u64_safe_divmod;
use integer::u64_to_felt252;
use integer::u64_wide_mul;
use integer::u128_is_zero;
use integer::u128_safe_divmod;
use integer::u128_to_felt252;
use integer::u128_wide_mul;

fn main() {
    let u8_value = 0_u8;
    let u16_value = 0_u16;
    let u32_value = 0_u32;
    let u64_value = 0_u64;
    let u128_value = 0_u128;

    // u???_to_felt252()
    {
        let u8_felt: felt252 = u8_to_felt252(u8_value);
        let u16_felt: felt252 = u16_to_felt252(u16_value);
        let u32_felt: felt252 = u32_to_felt252(u32_value);
        let u64_felt: felt252 = u64_to_felt252(u64_value);
        let u128_felt: felt252 = u128_to_felt252(u128_value);
    }

    // u???_wide_mul()
    {
        let u8_mul: u16 = u8_wide_mul(u8_value, u8_value);
        let u16_mul: u32 = u16_wide_mul(u16_value, u16_value);
        let u32_mul: u64 = u32_wide_mul(u32_value, u32_value);
        let u64_mul: u128 = u64_wide_mul(u64_value, u64_value);
        let (u128_mul_hi, u128_mul_lo): (u128, u128) = u128_wide_mul(u128_value, u128_value);
    }

    // u???_safe_divmod()
    //{
    //    let (u8_div_q, u8_div_r): (u8, u8) = u8_safe_divmod(u8_value, u8_to_nonzero(1_u8));
    //    let (u16_div_q, u16_div_r): (u16, u16) = u16_safe_divmod(u16_value, u16_to_nonzero(1_u16));
    //    let (u32_div_q, u32_div_r): (u32, u32) = u32_safe_divmod(u32_value, u32_to_nonzero(1_u32));
    //    let (u64_div_q, u64_div_r): (u64, u64) = u64_safe_divmod(u64_value, u64_to_nonzero(1_u64));
    //    let (u128_div_q, u128_div_r): (u128, u128) = u128_safe_divmod(
    //        u128_value, u128_to_nonzero(1_u128)
    //    );
    //}
}

//fn u8_to_nonzero(value: u8) -> NonZero<u8> {
//    match u8_is_zero(value) {
//        IsZeroResult::Zero(()) => panic(ArrayTrait::new()),
//        IsZeroResult::NonZero(x) => x,
//    }
//}
//
//fn u16_to_nonzero(value: u16) -> NonZero<u16> {
//    match u16_is_zero(value) {
//        IsZeroResult::Zero(()) => panic(ArrayTrait::new()),
//        IsZeroResult::NonZero(x) => x,
//    }
//}
//
//fn u32_to_nonzero(value: u32) -> NonZero<u32> {
//    match u32_is_zero(value) {
//        IsZeroResult::Zero(()) => panic(ArrayTrait::new()),
//        IsZeroResult::NonZero(x) => x,
//    }
//}
//
//fn u64_to_nonzero(value: u64) -> NonZero<u64> {
//    match u64_is_zero(value) {
//        IsZeroResult::Zero(()) => panic(ArrayTrait::new()),
//        IsZeroResult::NonZero(x) => x,
//    }
//}
//
//fn u128_to_nonzero(value: u128) -> NonZero<u128> {
//    match u128_is_zero(value) {
//        IsZeroResult::Zero(()) => panic(ArrayTrait::new()),
//        IsZeroResult::NonZero(x) => x,
//    }
//}
