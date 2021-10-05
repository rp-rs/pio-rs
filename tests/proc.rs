#[test]
fn test_pio_proc() {
    let p = pio_proc::pio!(
        1,
        "
    label:
        jmp label
    "
    );
    assert_eq!(p.program.origin, None);
    assert_eq!(&*p.program.code, &[0u16]);
    assert_eq!(
        p.program.wrap,
        pio::Wrap {
            source: 0,
            target: 0
        }
    );
}

#[test]
fn test_pio_proc2() {
    let p = pio_proc::pio!(
        32,
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
    assert_eq!(p.program.origin, Some(5));
    assert_eq!(&*p.program.code, &[0, 0]);
    assert_eq!(
        p.program.wrap,
        pio::Wrap {
            source: 0,
            target: 0
        }
    );
    assert_eq!(p.public_defines.label, 0);
    assert_eq!(p.public_defines.owo, 2);
}

#[test]
fn test_pio_proc_size() {
    // Inline constant size
    pio_proc::pio!(32, "label:\njmp label\n");
    // Constant variable
    const PROGRAM_SIZE: usize = 32;
    pio_proc::pio!(PROGRAM_SIZE, "label:\njmp label\n");
    // Expression
    pio_proc::pio!(10 + 20, "label:\njmp label\n");
    // Constant from another crate
    pio_proc::pio!(pio::RP2040_MAX_PROGRAM_SIZE, "label:\njmp label\n");
}
