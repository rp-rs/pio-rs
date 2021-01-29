#[macro_use]
extern crate pretty_assertions;

#[test_generator::test_resources("tests/pico-examples/*.pio")]
fn test(test: &str) {
    let path = std::path::PathBuf::from(test);
    let program_source = std::fs::read_to_string(&path).unwrap();
    let programs = pio::Program::parse_file(&program_source).unwrap();

    let mut hex_path = path;
    hex_path.set_extension("hex");

    if let Ok(hex_source) = std::fs::read_to_string(hex_path) {
        let mut hex_programs = vec![];
        for line in hex_source.lines() {
            if line.starts_with(".program") {
                hex_programs.push(vec![]);
            } else {
                hex_programs
                    .last_mut()
                    .unwrap()
                    .push(u16::from_str_radix(line, 16).unwrap());
            }
        }

        for (i, h) in hex_programs.iter().enumerate() {
            assert_eq!(programs[i].code(), h);
        }
    }
}
