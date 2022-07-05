#[test]
fn test_file() {
    let p = pio_proc::pio_file!(
        "./tests/test.pio",
        select_program("test2"),
        options(max_program_size = 32)
    );
    let p2 = pio_proc::pio_file!(
        "./tests/test.pio",
        select_program("test"),
        options(max_program_size = 32)
    );
    assert_eq!(p.public_defines.foo, 3);
    assert_eq!(p2.public_defines.foo, 3);
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
fn test_pio_proc() {
    let p = pio_proc::pio_asm!("label:", "jmp label", options(max_program_size = 1));
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
    let p = pio_proc::pio_asm!(
        ".origin 5",
        "public label:",
        "    .wrap_target",
        "    jmp label",
        "    .wrap",
        "    jmp label",
        ".define public owo label + 2",
        options(max_program_size = 32)
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
    pio_proc::pio_asm!("label:", "jmp label", options(max_program_size = 32));

    // Constant variable
    const PROGRAM_SIZE: usize = 32;
    pio_proc::pio_asm!(
        "label:",
        "jmp label",
        options(max_program_size = PROGRAM_SIZE)
    );

    // Expression
    pio_proc::pio_asm!("label:", "jmp label", options(max_program_size = 10 + 20));

    // Constant from another crate
    pio_proc::pio_asm!(
        "label:",
        "jmp label",
        options(max_program_size = pio::RP2040_MAX_PROGRAM_SIZE)
    );
}
