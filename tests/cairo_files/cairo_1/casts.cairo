use integer::upcast;

fn main() {
    let x8 = 0_u8;
    let x16 = 0_u16;
    let x32 = 0_u32;
    let x64 = 0_u64;
    let x128 = 0_u128;

    let x8_to_8: u8 = upcast(x8);
    let x8_to_16: u16 = upcast(x8);
    let x8_to_32: u32 = upcast(x8);
    let x8_to_64: u64 = upcast(x8);
    let x8_to_128: u128 = upcast(x8);

    let x16_to_16: u16 = upcast(x16);
    let x16_to_32: u32 = upcast(x16);
    let x16_to_64: u64 = upcast(x16);
    let x16_to_128: u128 = upcast(x16);

    let x32_to_32: u32 = upcast(x32);
    let x32_to_64: u64 = upcast(x32);
    let x32_to_128: u128 = upcast(x32);

    let x64_to_64: u64 = upcast(x64);
    let x64_to_128: u128 = upcast(x64);

    let x128_to_128: u128 = upcast(x128);
}
