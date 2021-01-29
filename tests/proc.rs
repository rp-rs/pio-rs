#[test]
fn test_pio_proc() {
    let p = pio_proc::pio!(
        "
    label:
        jmp label
    "
    );
    assert_eq!(p.origin(), None);
    assert_eq!(p.code(), &[0]);
    assert_eq!(p.wrap(), (0, 0));
}

#[test]
fn test_pio_proc2() {
    let p = pio_proc::pio!(
        "
    .origin 5
    public label:
        .wrap_target
        jmp label
        .wrap
        jmp label
    .define public owo label + 2
    "
    );
    assert_eq!(p.origin(), Some(5));
    assert_eq!(p.code(), &[0, 0]);
    assert_eq!(p.wrap(), (0, 0));
    assert_eq!(p.public_defines().label, 0);
    assert_eq!(p.public_defines().owo, 2);
}
