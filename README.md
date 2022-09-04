# pio-rs

Support for the Raspberry Silicon RP2040's *PIO* State Machines.

## What is PIO?

See https://www.raspberrypi.com/news/what-is-pio/. You can also read the PIO
section in the (very well written) RP2040 datasheet:
https://datasheets.raspberrypi.org/rp2040/rp2040-datasheet.pdf.

## What is pio-rs?

PIO programs must be compiled from PIO Assembly Language into a special PIO
machine code. This machine code is then stored in your C or Rust program, and
program is copied to the PIO hardware at the relevant point in time.

Raspberry Pi provide a PIO assembler called pioasm, and it lives at
https://github.com/raspberrypi/pico-sdk/tree/master/tools/pioasm. This is an
excellent choice if you want use the Raspberry Pi Pico SDK
(https://github.com/raspberrypi/pico-sdk) to write C or C++ programs for your
RP2040.

The pio-rs project provides an alternative implementation of pioasm. The main
benefits are:

* It's easier to integrate into an Embedded Rust program for the RP2040 than
  `pioasm`
* The compiler itself can be included in your Embedded Rust program, so you can
  compile PIO code on the RP2040, at run-time!
* Writing an assembler was a good way to test our understanding of the
  specification.
* It's written in Rust :)

## How do I use pio-rs?

If you want to write a program in Rust that uses the RP2040's PIO block, there
are three ways to use pio-rs:

### pio!

There is a macro called `pio!` which allows you to place PIO assembly language
source into your Rust program. This source code is assembled into a PIO program
at compile time.

Your `Cargo.toml` file should include:

```toml
[dependencies]
pio-proc = "0.2"
pio = "0.2"
```

Your Rust program should contain your PIO program, as follows with PIO asm directly in the file:

```rust
use pio_proc::pio_asm;

let program_with_defines = pio_proc::pio_asm!(
    "set pindirs, 1",
    ".wrap_target",
    "set pins, 0 [31]",
    "set pins, 1 [31]",
    ".wrap",
    options(max_program_size = 32) // Optional, defaults to 32
);
let program = program_with_defines.program;
```

Or you can assemble a stand-alone PIO file from disk:

```rust
use pio_proc::pio_file;

let program_with_defines = pio_proc::pio_file!(
    "./tests/test.pio",
    select_program("test"), // Optional if only one program in the file
    options(max_program_size = 32) // Optional, defaults to 32
);
let program = program_with_defines.program;
```

The syntax should be the same as supported by the official pioasm tool.

### pio::Assembler::new()

You can call `pio::Assembler::new()` and construct a PIO program using
the 'builder pattern' - effectively you are compiling a PIO program at
run-time on the RP2040 itself!

```rust
// Define some simple PIO program.
const MAX_DELAY: u8 = 31;
let mut assembler = pio::Assembler::<32>::new();
let mut wrap_target = assembler.label();
let mut wrap_source = assembler.label();
// Set pin as Out
assembler.set(pio::SetDestination::PINDIRS, 1);
// Define begin of program loop
assembler.bind(&mut wrap_target);
// Set pin low
assembler.set_with_delay(pio::SetDestination::PINS, 0, MAX_DELAY);
// Set pin high
assembler.set_with_delay(pio::SetDestination::PINS, 1, MAX_DELAY);
// Define end of program loop
assembler.bind(&mut wrap_source);
// The labels wrap_target and wrap_source, as set above,
// define a loop which is executed repeatedly by the PIO
// state machine.
let program = assembler.assemble_with_wrap(wrap_source, wrap_target);
```

Each line starting `assembler.` adds a new line to the program. The completed
program can be passed to the PIO driver in the Rust-language [RP2040
HAL](https://docs.rs/rp2040-hal/).

## PIO Examples

This crate is just the PIO assembler. If you want to see some fully-featured
PIO examples integrated with Embedded Rust on the RP2040, check out the
[rp-hal examples](https://github.com/rp-rs/rp-hal/tree/main/rp2040-hal/examples).

## Roadmap

NOTE This tool is under active development. As such, it is likely to remain
volatile until a 1.0.0 release.

See the [open issues](https://github.com/rp-rs/pio-rs/issues) for a list of
proposed features (and known issues).

## Contributing

Contributions are what make the open source community such an amazing place to
be learn, inspire, and create. Any contributions you make are **greatly
appreciated**.

1. Fork the Project
2. Create your Feature Branch (`git checkout -b feature/AmazingFeature`)
3. Commit your Changes (`git commit -m 'Add some AmazingFeature'`)
4. Push to the Branch (`git push origin feature/AmazingFeature`)
5. Open a Pull Request

## License

Distributed under the MIT License. See `LICENSE` for more information.

## Contact

Project Link: [https://github.com/rp-rs/pio-rs/issues](https://github.com/rp-rs/pio-rs/issues)
Matrix: [#rp-rs:matrix.org](https://matrix.to/#/#rp-rs:matrix.org)

## Acknowledgements

* [pioasm](https://github.com/raspberrypi/pico-sdk/tree/master/tools/pioasm)
