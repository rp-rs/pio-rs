#[macro_use]
extern crate pretty_assertions;

use std::{collections::HashMap, fs, path::PathBuf};

#[test_generator::test_resources("tests/pico-examples/*.pio")]
fn test(test: &str) {
    let path = PathBuf::from(test);
    let program_source = fs::read_to_string(&path).unwrap();
    let programs =
        pio_parser::Parser::<{ pio::RP2040_MAX_PROGRAM_SIZE }>::parse_file(&program_source)
            .unwrap();

    let mut hex_path = path;
    hex_path.set_extension("hex");

    if let Ok(hex_source) = fs::read_to_string(hex_path) {
        let mut hex_programs = HashMap::new();
        let mut current_program = String::new();

        for line in hex_source.lines() {
            if let Some(new_program) = line.strip_prefix(".program ") {
                current_program = new_program.into();
                hex_programs.insert(current_program.clone(), vec![]);
            } else {
                hex_programs
                    .get_mut(&current_program)
                    .unwrap()
                    .push(u16::from_str_radix(line, 16).unwrap());
            }
        }

        for (name, prog) in hex_programs.iter() {
            let program = programs.get(name).unwrap();
            assert_eq!(&*program.program.code, prog);
        }
    }
}
