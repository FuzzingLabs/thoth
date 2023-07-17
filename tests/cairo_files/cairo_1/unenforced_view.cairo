#[contract]
mod UnenforcedView {
    struct Storage {
        value: felt252,
    }

    #[view]
    fn writes_to_storage_indirect(val: felt252) {
       f1(val);
    }

    fn f1(val: felt252) {
        f2(val);
    }


    fn f2(val: felt252) {
        value::write(val);
    }

    #[view]
    fn writes_to_storage_direct(val:felt252) {
        value::write(val);
    }

    #[view]
    fn recursive_storage_write_direct(val: felt252) {
        if val ==0 {
            ()
        }
        value::write(val);
        recursive_storage_write_direct(val-1);
    }

    #[view]
    fn recursive_storage_write_indirect(val: felt252) {
        if val ==0 {
            ()
        }
        f3(val);
    }

    fn f3(val: felt252) {
        value::write(val);
        recursive_storage_write_indirect(val-1);
    }


    #[view]
    fn does_not_write_to_storage() -> felt252 {
        value::read()
    }
}



