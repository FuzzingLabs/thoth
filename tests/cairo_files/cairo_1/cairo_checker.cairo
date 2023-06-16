fn thoth_test_sum(mut a: felt252, mut b: felt252) {
   let sum = a + b;
   assert(sum == 10, '');
}
