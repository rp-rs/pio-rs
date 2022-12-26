# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.2.1] [Crates.io](https://crates.io/crates/pio-rs/0.2.1) [Github](https://github.com/rp-rs/pio-rs/releases/tag/v0.2.1)

- Fixed the search path for `pio_file` when using relative paths
- Check that the irq specified in a wait command is valid
- rename ParsedInstruction refiy method to reify
- Fix global directive newlines error
- Use (rel)ative bit for IRQ WaitSource
- disambiguate the use of pio_proc macros vs pio::Assembler
- Limit valid range if irqs for wait command
- Enable constant encoding for InstructionOperands
- Support `//` comments in .pio files

## [0.2.0] [Crates.io](https://crates.io/crates/pio-rs/0.2.0) [Github](https://github.com/rp-rs/pio-rs/releases/tag/v0.2.0)

- Updated syntax to allow for `.pio` files
- Updated pio asm macro with new syntax to follow `asm!`
- Add optional `rel` flag to index on `WAIT IRQ` instruction. (Breaking change, adds parameter to public data structures)

## [0.1.0] [Crates.io](https://crates.io/crates/pio-rs/0.1.0) [Github](https://github.com/rp-rs/pio-rs/releases/tag/v0.1.0)

- First release

[Unreleased]: https://github.com/rp-rs/pio-rs/compare/v0.2.1...HEAD
[0.2.1]: https://github.com/rp-rs/pio-rs/tag/v0.2.1
[0.2.0]: https://github.com/rp-rs/pio-rs/tag/v0.2.0
[0.1.0]: https://github.com/rp-rs/pio-rs/tag/v0.1.0
