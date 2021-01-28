use pio::parser::Program;

#[test]
fn test() -> Result<(), Box<dyn std::error::Error>> {
    let mut d = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("tests/pico-examples");

    for entry in std::fs::read_dir(d)? {
        let entry = entry?;
        let path = entry.path();
        if !path.to_str().unwrap().ends_with(".pio") {
            continue;
        }

        println!("testing {:?}", path);

        let program_source = std::fs::read_to_string(&path)?;
        let p = Program::parse_file(&program_source).unwrap().swap_remove(0);

        let mut hex_path = path.clone();
        hex_path.set_extension("hex");

        // FIXME: `pioasm` doesn't support emitting hex for multiple
        // programs in one file, so multi-program files are never
        // tested for correct instruction emit here.
        if let Ok(hex_source) = std::fs::read_to_string(hex_path) {
            let hex: Vec<u16> = hex_source
                .lines()
                .map(|l| u16::from_str_radix(l, 16).unwrap())
                .collect();
            assert_eq!(p.code(), hex);
        }
    }
    Ok(())
}
