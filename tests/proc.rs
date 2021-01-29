#[test]
fn test_pio_proc() {
    let p = pio_proc::pio!(
        "
    label:
        jmp label
    "
    );
    assert_eq!(p.code(), &[0])
}
