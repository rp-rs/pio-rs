fn main() {
    #[cfg(not(feature = "rp2350"))]
    lalrpop::Configuration::new()
        .set_out_dir(std::env::var("OUT_DIR").unwrap())
        .process_file("src/rp2040.lalrpop")
        .unwrap();
    #[cfg(feature = "rp2350")]
    lalrpop::Configuration::new()
        .set_out_dir(std::env::var("OUT_DIR").unwrap())
        .process_file("src/rp2350.lalrpop")
        .unwrap();
}
