enum MyEnum {
    A: u8,
    B: u16,
    C: u32,
    D: u64
}

fn my_enum_a() -> MyEnum {
    MyEnum::A(4_u8)
}

fn my_enum_b() -> MyEnum {
    MyEnum::B(8_u16)
}

fn my_enum_c() -> MyEnum {
    MyEnum::C(16_u32)
}

fn my_enum_d() -> MyEnum {
    MyEnum::D(16_u64)
}

fn main() -> MyEnum {
    MyEnum::D(16_u64)
}
