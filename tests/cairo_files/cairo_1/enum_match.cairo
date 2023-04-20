enum MyEnum {
    A: u8,
    B: u16,
    C: u32,
}

fn get_my_enum_b(x: MyEnum) -> u16 {
    match x {
        MyEnum::A(x) => 1_u16,
        MyEnum::B(x) => x,
        MyEnum::C(x) => 0_u16,
    }
}

fn main() -> u16 {
    get_my_enum_b(MyEnum::B(16_u16))
}
