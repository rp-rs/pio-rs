use pio::parser::Program;

#[test]
fn test() -> Result<(), Box<dyn std::error::Error>> {
    let mut d = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("tests/pico-examples");

    for entry in std::fs::read_dir(d)? {
        let entry = entry?;
        let path = entry.path();
        if !path.to_str().unwrap().ends_with(".hex") {
            continue;
        }

        let mut prog_path = path.clone();
        prog_path.set_extension("pio");

        println!("testing {:?}", prog_path);

        let program_source = std::fs::read_to_string(&prog_path)?;
        let p = Program::parse_file(&program_source).unwrap();
        println!("{:?}", p);

        // let hex_source = std::fs::read_to_string(&path)?;
    }
    Ok(())
}
