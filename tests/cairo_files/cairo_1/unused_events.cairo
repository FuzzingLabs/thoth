#[contract]
mod UnusedEvents {
    #[event]
    fn MyUnusedEvent(value: u256) {}

    #[event]
    fn MyUsedEvent(value: u256) {}

    #[external]
    fn use_event(amount: u256) {
        MyUsedEvent(amount);
    }
}
