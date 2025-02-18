//! # Programmable Input/Output
//!
//! ```rust
//! // Repeatedly get one word of data from the TX FIFO, stalling when
//! // the FIFO is empty. Write the least significant bit to the OUT pin
//! // group.
//! // https://github.com/raspberrypi/pico-examples/tree/master/pio/hello_pio/hello.pio
//! let mut a = pio::Assembler::<{ pio::RP2040_MAX_PROGRAM_SIZE }>::new();
//!
//! let mut loop_label = a.label();
//!
//! a.bind(&mut loop_label);
//! a.pull(false, false);
//! a.out(pio::OutDestination::PINS, 1);
//! a.jmp(pio::JmpCondition::Always, &mut loop_label);
//!
//! let program = a.assemble_program();
//! ```
//!
//! ## Wrapping
//! ```rust
//! let mut a = pio::Assembler::<{ pio::RP2040_MAX_PROGRAM_SIZE }>::new();
//!
//! let mut wrap_source = a.label();
//! let mut wrap_target = a.label();
//!
//! // Initialize pin direction only once
//! a.set(pio::SetDestination::PINDIRS, 1);
//! a.bind(&mut wrap_target);
//! a.out(pio::OutDestination::PINS, 1);
//! a.bind(&mut wrap_source);
//!
//! let program = a.assemble_with_wrap(wrap_source, wrap_target);
//! ```

#![no_std]

pub use pio_core::*;

/// Not covered by semver guarantees
#[doc(hidden)]
pub mod _export {
    pub use pio_proc::*;
}

#[macro_export]
macro_rules! pio_asm {
    ($($t:tt)*) => {
        $crate::_export::pio_asm_inner!($crate, $($t)*)
    };
}

#[macro_export]
macro_rules! pio_file {
    ($($t:tt)*) => {
        $crate::_export::pio_file_inner!($crate, $($t)*)
    };
}
