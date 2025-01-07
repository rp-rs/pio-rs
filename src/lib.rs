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
// PIO instr grouping is 3/5/3/5
#![allow(clippy::unusual_byte_groupings)]
#![allow(clippy::upper_case_acronyms)]

pub use arrayvec::ArrayVec;
use core::convert::TryFrom;
use num_enum::TryFromPrimitive;

/// Maximum program size of RP2040 and RP235x chips, in bytes.
///
/// See Chapter 3, Figure 38 for reference of the value.
pub const RP2040_MAX_PROGRAM_SIZE: usize = 32;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
/// PIO version
pub enum PioVersion {
    /// Pio programs compatable with the RP2040
    V0,
    /// Pio programs compatable with both the RP2040 and RP235x
    V1,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, TryFromPrimitive, PartialEq, Eq)]
pub enum JmpCondition {
    /// Always
    Always = 0b000,
    /// `!X`: scratch X zero
    XIsZero = 0b001,
    /// `X--`: scratch X non-zero, post decrement
    XDecNonZero = 0b010,
    /// `!Y`: scratch Y zero
    YIsZero = 0b011,
    /// `Y--`: scratch Y non-zero, post decrement
    YDecNonZero = 0b100,
    /// `X!=Y`: scratch X not equal to scratch Y
    XNotEqualY = 0b101,
    /// `PIN`: branch on input pin
    PinHigh = 0b110,
    /// `!OSRE`: output shift register not empty
    OutputShiftRegisterNotEmpty = 0b111,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, TryFromPrimitive, PartialEq, Eq)]
pub enum WaitSource {
    GPIO = 0b00,
    PIN = 0b01,
    IRQ = 0b10,
    JMPPIN = 0b11,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, TryFromPrimitive, PartialEq, Eq)]
pub enum InSource {
    PINS = 0b000,
    X = 0b001,
    Y = 0b010,
    NULL = 0b011,
    // RESERVED = 0b100,
    // RESERVED = 0b101,
    ISR = 0b110,
    OSR = 0b111,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, TryFromPrimitive, PartialEq, Eq)]
pub enum OutDestination {
    PINS = 0b000,
    X = 0b001,
    Y = 0b010,
    NULL = 0b011,
    PINDIRS = 0b100,
    PC = 0b101,
    ISR = 0b110,
    EXEC = 0b111,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, TryFromPrimitive, PartialEq, Eq)]
pub enum MovDestination {
    PINS = 0b000,
    X = 0b001,
    Y = 0b010,
    PINDIRS = 0b011,
    EXEC = 0b100,
    PC = 0b101,
    ISR = 0b110,
    OSR = 0b111,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, TryFromPrimitive, PartialEq, Eq)]
pub enum MovOperation {
    None = 0b00,
    Invert = 0b01,
    BitReverse = 0b10,
    // RESERVED = 0b11,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, TryFromPrimitive, PartialEq, Eq)]
pub enum MovSource {
    PINS = 0b000,
    X = 0b001,
    Y = 0b010,
    NULL = 0b011,
    // RESERVED = 0b100,
    STATUS = 0b101,
    ISR = 0b110,
    OSR = 0b111,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, TryFromPrimitive, PartialEq, Eq)]
pub enum MovRxIndex {
    RXFIFOY = 0b0000,
    RXFIFO0 = 0b1000,
    RXFIFO1 = 0b1001,
    RXFIFO2 = 0b1010,
    RXFIFO3 = 0b1011,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, TryFromPrimitive, PartialEq, Eq)]
pub enum SetDestination {
    PINS = 0b000,
    X = 0b001,
    Y = 0b010,
    // RESERVED = 0b011,
    PINDIRS = 0b100,
    // RESERVED = 0b101,
    // RESERVED = 0b110,
    // RESERVED = 0b111,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, TryFromPrimitive, PartialEq, Eq)]
pub enum IrqIndexMode {
    DIRECT = 0b00,
    PREV = 0b01,
    REL = 0b10,
    NEXT = 0b11,
}

#[derive(Debug, Clone, Copy)]
pub enum InstructionOperands {
    JMP {
        condition: JmpCondition,
        address: u8,
    },
    WAIT {
        /// 1 -> wait for 1
        /// 0 -> wait for 0
        polarity: u8,
        source: WaitSource,
        index: u8,
        relative: bool,
    },
    IN {
        source: InSource,
        bit_count: u8,
    },
    OUT {
        destination: OutDestination,
        bit_count: u8,
    },
    PUSH {
        if_full: bool,
        block: bool,
    },
    PULL {
        if_empty: bool,
        block: bool,
    },
    MOV {
        destination: MovDestination,
        op: MovOperation,
        source: MovSource,
    },
    MOVTORX {
        fifo_index: MovRxIndex,
    },
    MOVFROMRX {
        fifo_index: MovRxIndex,
    },
    IRQ {
        clear: bool,
        wait: bool,
        index: u8,
        index_mode: IrqIndexMode,
    },
    SET {
        destination: SetDestination,
        data: u8,
    },
}

impl InstructionOperands {
    const fn discrim(&self) -> u16 {
        match self {
            InstructionOperands::JMP { .. } => 0b000,
            InstructionOperands::WAIT { .. } => 0b001,
            InstructionOperands::IN { .. } => 0b010,
            InstructionOperands::OUT { .. } => 0b011,
            InstructionOperands::PUSH { .. } => 0b100,
            InstructionOperands::PULL { .. } => 0b100,
            InstructionOperands::MOV { .. } => 0b101,
            InstructionOperands::MOVTORX { .. } => 0b100,
            InstructionOperands::MOVFROMRX { .. } => 0b100,
            InstructionOperands::IRQ { .. } => 0b110,
            InstructionOperands::SET { .. } => 0b111,
        }
    }

    const fn operands(&self) -> (u8, u8) {
        match self {
            InstructionOperands::JMP { condition, address } => (*condition as u8, *address),
            InstructionOperands::WAIT {
                polarity,
                source,
                index,
                relative,
            } => {
                if *relative && !matches!(*source, WaitSource::IRQ) {
                    panic!("relative flag should only be used with WaitSource::IRQ");
                }
                if matches!(*source, WaitSource::IRQ) && *index > 7 {
                    panic!("Index for WaitSource::IRQ should be in range 0..=7");
                }
                (
                    (*polarity) << 2 | (*source as u8),
                    *index | (if *relative { 0b10000 } else { 0 }),
                )
            }
            InstructionOperands::IN { source, bit_count } => {
                if *bit_count == 0 || *bit_count > 32 {
                    panic!("bit_count must be from 1 to 32");
                }
                (*source as u8, *bit_count & 0b11111)
            }
            InstructionOperands::OUT {
                destination,
                bit_count,
            } => {
                if *bit_count == 0 || *bit_count > 32 {
                    panic!("bit_count must be from 1 to 32");
                }
                (*destination as u8, *bit_count & 0b11111)
            }
            InstructionOperands::PUSH { if_full, block } => {
                ((*if_full as u8) << 1 | (*block as u8), 0)
            }
            InstructionOperands::PULL { if_empty, block } => {
                (1 << 2 | (*if_empty as u8) << 1 | (*block as u8), 0)
            }
            InstructionOperands::MOV {
                destination,
                op,
                source,
            } => (*destination as u8, (*op as u8) << 3 | (*source as u8)),
            InstructionOperands::MOVTORX { fifo_index } => (0, 1 << 4 | *fifo_index as u8),
            InstructionOperands::MOVFROMRX { fifo_index } => (0b100, 1 << 4 | *fifo_index as u8),
            InstructionOperands::IRQ {
                clear,
                wait,
                index,
                index_mode,
            } => {
                if *index > 7 {
                    panic!("invalid interrupt flags");
                }
                (
                    (*clear as u8) << 1 | (*wait as u8),
                    *index | (*index_mode as u8) << 3,
                )
            }
            InstructionOperands::SET { destination, data } => {
                if *data > 0x1f {
                    panic!("SET argument out of range");
                }
                (*destination as u8, *data)
            }
        }
    }

    /// Encode these operands into binary representation.
    /// Note that this output does not take side set and delay into account.
    pub const fn encode(&self) -> u16 {
        let mut data: u16 = 0;
        data |= self.discrim() << 13;
        let (o0, o1) = self.operands();
        data |= (o0 as u16) << 5;
        data |= o1 as u16;
        data
    }

    /// Decode operands from binary representation.
    /// Note that this output does not take side set and delay into account.
    pub fn decode(instruction: u16) -> Option<Self> {
        let discrim = instruction >> 13;
        let o0 = ((instruction >> 5) & 0b111) as u8;
        let o1 = (instruction & 0b11111) as u8;

        match discrim {
            0b000 => JmpCondition::try_from(o0)
                .ok()
                .map(|condition| InstructionOperands::JMP {
                    condition,
                    address: o1,
                }),
            0b001 => {
                WaitSource::try_from(o0 & 0b011)
                    .ok()
                    .map(|source| InstructionOperands::WAIT {
                        polarity: o0 >> 2,
                        source,
                        index: if source == WaitSource::IRQ {
                            o1 & 0b00111
                        } else {
                            o1
                        },
                        relative: source == WaitSource::IRQ && (o1 & 0b10000) != 0,
                    })
            }
            0b010 => InSource::try_from(o0)
                .ok()
                .map(|source| InstructionOperands::IN {
                    source,
                    bit_count: if o1 == 0 { 32 } else { o1 },
                }),
            0b011 => {
                OutDestination::try_from(o0)
                    .ok()
                    .map(|destination| InstructionOperands::OUT {
                        destination,
                        bit_count: if o1 == 0 { 32 } else { o1 },
                    })
            }
            0b100 => {
                let p_o0 = ((instruction >> 4) & 0b1111) as u8;

                let if_flag = p_o0 & 0b0100 != 0;
                let block = p_o0 & 0b0010 != 0;

                let index = MovRxIndex::try_from((instruction & 0b1111) as u8);
                if p_o0 & 0b1001 == 0b1000 {
                    Some(InstructionOperands::PULL {
                        if_empty: if_flag,
                        block,
                    })
                } else if p_o0 & 0b1001 == 0b0000 {
                    Some(InstructionOperands::PUSH {
                        if_full: if_flag,
                        block,
                    })
                } else if p_o0 == 0b1001 {
                    Some(InstructionOperands::MOVFROMRX {
                        fifo_index: index.ok()?,
                    })
                } else if p_o0 == 0b0001 {
                    Some(InstructionOperands::MOVTORX {
                        fifo_index: index.ok()?,
                    })
                } else {
                    None
                }
            }
            0b101 => match (
                MovDestination::try_from(o0).ok(),
                MovOperation::try_from((o1 >> 3) & 0b11).ok(),
                MovSource::try_from(o1 & 0b111).ok(),
            ) {
                (Some(destination), Some(op), Some(source)) => Some(InstructionOperands::MOV {
                    destination,
                    op,
                    source,
                }),
                _ => None,
            },
            0b110 => {
                if o0 & 0b100 == 0 {
                    let index_mode = IrqIndexMode::try_from((o1 >> 3) & 0b11);
                    Some(InstructionOperands::IRQ {
                        clear: o0 & 0b010 != 0,
                        wait: o0 & 0b001 != 0,
                        index: o1 & 0b00111,
                        index_mode: index_mode.ok()?,
                    })
                } else {
                    None
                }
            }
            0b111 => {
                SetDestination::try_from(o0)
                    .ok()
                    .map(|destination| InstructionOperands::SET {
                        destination,
                        data: o1,
                    })
            }
            _ => None,
        }
    }
}

/// A PIO instruction.
#[derive(Debug, Clone, Copy)]
pub struct Instruction {
    pub operands: InstructionOperands,
    pub delay: u8,
    pub side_set: Option<u8>,
}

impl Instruction {
    /// Encode a single instruction.
    pub fn encode(&self, side_set: SideSet) -> u16 {
        let delay_max = (1 << (5 - side_set.bits)) - 1;
        let mut data = self.operands.encode();

        if self.delay > delay_max {
            panic!(
                "delay of {} is greater than limit {}",
                self.delay, delay_max
            );
        }

        let side_set = if let Some(s) = self.side_set {
            if s > side_set.max {
                panic!("'side' set must be >=0 and <={}", side_set.max);
            }
            let s = (s as u16) << (5 - side_set.bits);
            if side_set.opt {
                s | 0b10000
            } else {
                s
            }
        } else if side_set.bits > 0 && !side_set.opt {
            panic!("instruction requires 'side' set");
        } else {
            0
        };

        data |= ((self.delay as u16) | side_set) << 8;

        data
    }

    /// Decode a single instruction.
    pub fn decode(instruction: u16, side_set: SideSet) -> Option<Instruction> {
        InstructionOperands::decode(instruction).map(|operands| {
            let data = ((instruction >> 8) & 0b11111) as u8;

            let delay = data & ((1 << (5 - side_set.bits)) - 1);

            let has_side_set = side_set.bits > 0 && (!side_set.opt || data & 0b10000 > 0);
            let side_set_data =
                (data & if side_set.opt { 0b01111 } else { 0b11111 }) >> (5 - side_set.bits);

            let side_set = if has_side_set {
                Some(side_set_data)
            } else {
                None
            };

            Instruction {
                operands,
                delay,
                side_set,
            }
        })
    }
}

#[derive(Debug)]
enum LabelState {
    Unbound(u8),
    Bound(u8),
}

/// A label.
#[derive(Debug)]
pub struct Label {
    state: LabelState,
}

impl Drop for Label {
    fn drop(&mut self) {
        if let LabelState::Unbound(_) = self.state {
            panic!("label was not bound");
        }
    }
}

/// Data for 'side' set instruction parameters.
#[derive(Debug, Clone, Copy)]
pub struct SideSet {
    opt: bool,
    bits: u8,
    max: u8,
    pindirs: bool,
}

impl SideSet {
    pub const fn new(opt: bool, bits: u8, pindirs: bool) -> SideSet {
        SideSet {
            opt,
            bits: bits + opt as u8,
            max: (1 << bits) - 1,
            pindirs,
        }
    }

    #[doc(hidden)]
    pub fn new_from_proc_macro(opt: bool, bits: u8, pindirs: bool) -> SideSet {
        SideSet {
            opt,
            bits,
            max: (1 << bits) - 1,
            pindirs,
        }
    }

    pub fn optional(&self) -> bool {
        self.opt
    }

    pub fn bits(&self) -> u8 {
        self.bits
    }

    pub fn pindirs(&self) -> bool {
        self.pindirs
    }
}

impl Default for SideSet {
    fn default() -> Self {
        SideSet::new(false, 0, false)
    }
}

/// A PIO Assembler. See chapter three of the [RP2040 Datasheet][].
///
/// [RP2040 Datasheet]: https://rptl.io/rp2040-datasheet
#[derive(Debug)]
pub struct Assembler<const PROGRAM_SIZE: usize> {
    #[doc(hidden)]
    pub instructions: ArrayVec<Instruction, PROGRAM_SIZE>,
    #[doc(hidden)]
    pub side_set: SideSet,
}

impl<const PROGRAM_SIZE: usize> Assembler<PROGRAM_SIZE> {
    /// Create a new Assembler.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Assembler::new_with_side_set(SideSet::default())
    }

    /// Create a new Assembler with `SideSet` settings.
    #[allow(clippy::new_without_default)]
    pub fn new_with_side_set(side_set: SideSet) -> Self {
        Assembler {
            instructions: ArrayVec::new(),
            side_set,
        }
    }

    /// Assemble the program into PIO instructions.
    pub fn assemble(self) -> ArrayVec<u16, PROGRAM_SIZE> {
        self.instructions
            .iter()
            .map(|i| i.encode(self.side_set))
            .collect()
    }

    /// Check the program for instructions and operands available only on the RP2350.
    pub fn version(&self) -> PioVersion {
        for instr in &self.instructions {
            let opr = instr.operands;
            match opr {
                InstructionOperands::MOVFROMRX { .. } => return PioVersion::V1,
                InstructionOperands::MOVTORX { .. } => return PioVersion::V1,
                InstructionOperands::MOV { destination, .. } => {
                    if destination == MovDestination::PINDIRS {
                        return PioVersion::V1;
                    }
                }
                InstructionOperands::WAIT { source, .. } => {
                    if source == WaitSource::JMPPIN {
                        return PioVersion::V1;
                    }
                }
                InstructionOperands::IRQ { index_mode, .. } => {
                    if index_mode == IrqIndexMode::PREV || index_mode == IrqIndexMode::NEXT {
                        return PioVersion::V1;
                    }
                }
                _ => (),
            }
        }

        PioVersion::V0
    }

    /// Assemble the program into [`Program`].
    ///
    /// The program contains the instructions and side-set info set. You can directly compile into a program with
    /// correct wrapping with [`Self::assemble_with_wrap`], or you can set the wrapping after the compilation with
    /// [`Program::set_wrap`].
    pub fn assemble_program(self) -> Program<PROGRAM_SIZE> {
        let side_set = self.side_set;
        let version = self.version();
        let code = self.assemble();
        let wrap = Wrap {
            source: (code.len() - 1) as u8,
            target: 0,
        };

        Program {
            code,
            origin: None,
            side_set,
            wrap,
            version,
        }
    }

    /// Assemble the program into [`Program`] with wrapping.
    ///
    /// Takes pair of labels controlling the wrapping. The first label is the source (top) of the wrap while the second
    /// label is the target (bottom) of the wrap. The source label should be positioned _after_ the instruction from
    /// which the wrapping happens.
    pub fn assemble_with_wrap(self, source: Label, target: Label) -> Program<PROGRAM_SIZE> {
        let source = self.label_offset(&source) - 1;
        let target = self.label_offset(&target);
        self.assemble_program().set_wrap(Wrap { source, target })
    }

    /// Get the offset of a label in the program.
    pub fn label_offset(&self, label: &Label) -> u8 {
        match &label.state {
            LabelState::Bound(offset) => *offset,
            LabelState::Unbound(_) => panic!("can't get offset for unbound label"),
        }
    }
}

impl<const PROGRAM_SIZE: usize> Assembler<PROGRAM_SIZE> {
    /// Create a new unbound Label.
    pub fn label(&mut self) -> Label {
        Label {
            state: LabelState::Unbound(u8::MAX),
        }
    }

    /// Create a new label bound to given offset.
    pub fn label_at_offset(&mut self, offset: u8) -> Label {
        Label {
            state: LabelState::Bound(offset),
        }
    }

    /// Bind `label` to the current instruction position.
    pub fn bind(&mut self, label: &mut Label) {
        match label.state {
            LabelState::Bound(_) => panic!("cannot bind label twice"),
            LabelState::Unbound(mut patch) => {
                let resolved_address = self.instructions.len() as u8;
                while patch != u8::MAX {
                    // SAFETY: patch points to the next instruction to patch
                    let instr = unsafe { self.instructions.get_unchecked_mut(patch as usize) };
                    if let InstructionOperands::JMP { address, .. } = &mut instr.operands {
                        patch = *address;
                        *address = resolved_address;
                    } else {
                        unreachable!();
                    }
                }
                label.state = LabelState::Bound(resolved_address);
            }
        }
    }
}

macro_rules! instr_impl {
    ( $(#[$inner:ident $($args:tt)*])* $name:ident ( $self:ident $(, $( $arg_name:ident : $arg_ty:ty ),*)? ) $body:expr, $delay:expr, $side_set:expr ) => {
        $(#[$inner $($args)*])*
        pub fn $name(
            &mut $self
            $(, $( $arg_name : $arg_ty , )*)?
        ) {
            $self.instructions.push(Instruction {
                operands: $body,
                delay: $delay,
                side_set: $side_set,
            })
        }
    }
}

macro_rules! instr {
    ( $(#[$inner:ident $($args:tt)*])* $name:ident ( $self:ident $(, $($arg_name:ident : $arg_ty:ty ),*)? ) $body:expr ) => {
        instr_impl!($(#[$inner $($args)*])* $name ( $self $(, $( $arg_name: $arg_ty ),*)? ) $body, 0, None );
        paste::paste! {
            instr_impl!($(#[$inner $($args)*])* [< $name _with_delay >] ( $self $(, $( $arg_name: $arg_ty ),*)? , delay: u8 ) $body, delay, None );
            instr_impl!($(#[$inner $($args)*])* [< $name _with_side_set >] ( $self $(, $( $arg_name: $arg_ty ),*)? , side_set: u8 ) $body, 0, Some(side_set) );
            instr_impl!($(#[$inner $($args)*])* [< $name _with_delay_and_side_set >] ( $self $(, $( $arg_name: $arg_ty ),*)? , delay: u8, side_set: u8 ) $body, delay, Some(side_set) );
        }
    }
}

impl<const PROGRAM_SIZE: usize> Assembler<PROGRAM_SIZE> {
    instr!(
        /// Emit a `jmp` instruction to `label` for `condition`.
        jmp(self, condition: JmpCondition, label: &mut Label) {
            let address = match label.state {
                LabelState::Unbound(a) => {
                    label.state = LabelState::Unbound(self.instructions.len() as u8);
                    a
                }
                LabelState::Bound(a) => a,
            };
            InstructionOperands::JMP {
                condition,
                address,
            }
        }
    );

    instr!(
        /// Emit a `wait` instruction with `polarity` from `source` with `index` which may be
        /// `relative`.
        wait(self, polarity: u8, source: WaitSource, index: u8, relative: bool) {
            InstructionOperands::WAIT {
                polarity,
                source,
                index,
                relative,
            }
        }
    );

    instr!(
        /// Emit an `in` instruction from `source` with `bit_count`.
        r#in(self, source: InSource, bit_count: u8) {
            InstructionOperands::IN { source, bit_count }
        }
    );

    instr!(
        /// Emit an `out` instruction to `source` with `bit_count`.
        out(self, destination: OutDestination, bit_count: u8) {
            InstructionOperands::OUT {
                destination,
                bit_count,
            }
        }
    );

    instr!(
        /// Emit a `push` instruction with `if_full` and `block`.
        push(self, if_full: bool, block: bool) {
            InstructionOperands::PUSH {
                if_full,
                block,
            }
        }
    );

    instr!(
        /// Emit a `pull` instruction with `if_empty` and `block`.
        pull(self, if_empty: bool, block: bool) {
            InstructionOperands::PULL {
                if_empty,
                block,
            }
        }
    );

    instr!(
        /// Emit a `mov` instruction to `destination` using `op` from `source`.
        mov(self, destination: MovDestination, op: MovOperation, source: MovSource) {
            InstructionOperands::MOV {
                destination,
                op,
                source,
            }
        }
    );

    instr!(
        /// Emit a `mov to rx` instruction.
        mov_to_rx(self, fifo_index: MovRxIndex) {
            InstructionOperands::MOVTORX {
                fifo_index
            }
        }
    );

    instr!(
        /// Emit a `mov from rx` instruction.
        mov_from_rx(self, fifo_index: MovRxIndex) {
            InstructionOperands::MOVFROMRX {
                fifo_index
            }
        }
    );

    instr!(
        /// Emit an `irq` instruction using `clear` and `wait` with `index` which may be `relative`.
        irq(self, clear: bool, wait: bool, index: u8, index_mode: IrqIndexMode) {
            InstructionOperands::IRQ {
                clear,
                wait,
                index,
                index_mode
            }
        }
    );

    instr!(
        /// Emit a `set` instruction
        set(self, destination: SetDestination, data: u8) {
            InstructionOperands::SET {
                destination,
                data,
            }
        }
    );

    instr!(
        /// Emit a `mov` instruction from Y to Y without operation effectively acting as a `nop`
        /// instruction.
        nop(self) {
            InstructionOperands::MOV {
                destination: MovDestination::Y,
                op: MovOperation::None,
                source: MovSource::Y
            }
        }
    );
}

/// Source and target for automatic program wrapping.
///
/// After the instruction at offset pointed by [`source`] has been executed, the program control flow jumps to the
/// instruction pointed by [`target`]. If the instruction is a jump, and the condition is true, the jump takes priority.
///
/// [`source`]: Self::source
/// [`target`]: Self::target
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Wrap {
    /// Source instruction for wrap.
    pub source: u8,
    /// Target instruction for wrap.
    pub target: u8,
}

/// Program ready to be executed by PIO hardware.
#[derive(Debug)]
pub struct Program<const PROGRAM_SIZE: usize> {
    /// Assembled program code.
    pub code: ArrayVec<u16, PROGRAM_SIZE>,
    /// Offset at which the program must be loaded.
    ///
    /// Most often 0 if defined. This might be needed when using data based `JMP`s.
    ///
    /// NOTE: Instruction addresses in JMP instructions as well as
    /// wrap source/target are calculated as if the origin was 0.
    /// Functions loading the program into PIO instruction memory will
    /// adjust those addresses accordingly if the program is loaded
    /// to a non-zero origin address.
    pub origin: Option<u8>,
    /// Wrapping behavior for this program.
    pub wrap: Wrap,
    /// Side-set info for this program.
    pub side_set: SideSet,
    /// Pio Version required for this program.
    pub version: PioVersion,
}

impl<const PROGRAM_SIZE: usize> Program<PROGRAM_SIZE> {
    /// Set the program loading location.
    ///
    /// If `None`, the program can be loaded at any location in the instruction memory.
    pub fn set_origin(self, origin: Option<u8>) -> Self {
        Self { origin, ..self }
    }

    /// Set the wrapping of the program.
    pub fn set_wrap(self, wrap: Wrap) -> Self {
        assert!((wrap.source as usize) < self.code.len());
        assert!((wrap.target as usize) < self.code.len());
        Self { wrap, ..self }
    }
}

/// Parsed program with defines.
pub struct ProgramWithDefines<PublicDefines, const PROGRAM_SIZE: usize> {
    /// The compiled program.
    pub program: Program<PROGRAM_SIZE>,
    /// Public defines.
    pub public_defines: PublicDefines,
}

#[test]
fn test_jump_1() {
    let mut a = Assembler::<32>::new();

    let mut l = a.label();
    a.set(SetDestination::X, 0);
    a.bind(&mut l);
    a.set(SetDestination::X, 1);
    a.jmp(JmpCondition::Always, &mut l);

    assert_eq!(
        a.assemble().as_slice(),
        &[
            0b111_00000_001_00000, // SET X 0
            // L:
            0b111_00000_001_00001, // SET X 1
            0b000_00000_000_00001, // JMP L
        ]
    );
}

#[test]
fn test_jump_2() {
    let mut a = Assembler::<32>::new();

    let mut top = a.label();
    let mut bottom = a.label();
    a.bind(&mut top);
    a.set(SetDestination::Y, 0);
    a.jmp(JmpCondition::YIsZero, &mut bottom);
    a.jmp(JmpCondition::Always, &mut top);
    a.bind(&mut bottom);
    a.set(SetDestination::Y, 1);

    assert_eq!(
        a.assemble().as_slice(),
        &[
            // TOP:
            0b111_00000_010_00000, // SET Y 0
            0b000_00000_011_00011, // JMP YIsZero BOTTOM
            0b000_00000_000_00000, // JMP Always TOP
            // BOTTOM:
            0b111_00000_010_00001, // SET Y 1
        ]
    );
}

#[test]
fn test_assemble_with_wrap() {
    let mut a = Assembler::<32>::new();

    let mut source = a.label();
    let mut target = a.label();

    a.set(SetDestination::PINDIRS, 0);
    a.bind(&mut target);
    a.r#in(InSource::NULL, 1);
    a.push(false, false);
    a.bind(&mut source);
    a.jmp(JmpCondition::Always, &mut target);

    assert_eq!(
        a.assemble_with_wrap(source, target).wrap,
        Wrap {
            source: 2,
            target: 1,
        }
    );
}

#[test]
fn test_assemble_program_default_wrap() {
    let mut a = Assembler::<32>::new();

    a.set(SetDestination::PINDIRS, 0);
    a.r#in(InSource::NULL, 1);
    a.push(false, false);

    assert_eq!(
        a.assemble_program().wrap,
        Wrap {
            source: 2,
            target: 0,
        }
    );
}

macro_rules! instr_test {
    ($name:ident ( $( $v:expr ),* ) , $expected:expr, $side_set:expr, $version:expr) => {
        paste::paste! {
            #[test]
            fn [< test _ $name _ $expected >]() {
                let expected = $expected;

                let mut a = Assembler::<32>::new_with_side_set($side_set);
                a.$name(
                    $( $v ),*
                );

                assert_eq!(a.version(), $version);

                let instr = a.assemble()[0];
                if instr != expected {
                    panic!("assertion failure: (left == right)\nleft:  {:#016b}\nright: {:#016b}", instr, expected);
                }

                let decoded = Instruction::decode(instr, $side_set).unwrap();
                let encoded = decoded.encode($side_set);
                if encoded != expected {
                    panic!("assertion failure: (left == right)\nleft:  {:#016b}\nright: {:#016b}", encoded, expected);
                }
            }
        }
    };

    ($name:ident ( $( $v:expr ),* ) , $b:expr, $version:expr) => {
        instr_test!( $name ( $( $v ),* ), $b, SideSet::new(false, 0, false), $version);
    };
}

instr_test!(
    wait(0, WaitSource::IRQ, 2, false),
    0b001_00000_010_00010,
    PioVersion::V0
);
instr_test!(
    wait(1, WaitSource::IRQ, 7, false),
    0b001_00000_110_00111,
    PioVersion::V0
);
instr_test!(
    wait(1, WaitSource::GPIO, 16, false),
    0b001_00000_100_10000,
    PioVersion::V0
);
instr_test!(
    wait_with_delay(0, WaitSource::IRQ, 2, false, 30),
    0b001_11110_010_00010,
    PioVersion::V0
);
instr_test!(
    wait_with_side_set(0, WaitSource::IRQ, 2, false, 0b10101),
    0b001_10101_010_00010,
    SideSet::new(false, 5, false),
    PioVersion::V0
);
instr_test!(
    wait(0, WaitSource::IRQ, 2, true),
    0b001_00000_010_10010,
    PioVersion::V0
);

#[test]
#[should_panic]
fn test_wait_relative_not_used_on_irq() {
    let mut a = Assembler::<32>::new();
    a.wait(0, WaitSource::PIN, 10, true);
    a.assemble_program();
}

instr_test!(r#in(InSource::Y, 10), 0b010_00000_010_01010, PioVersion::V0);
instr_test!(r#in(InSource::Y, 32), 0b010_00000_010_00000, PioVersion::V0);

instr_test!(
    out(OutDestination::Y, 10),
    0b011_00000_010_01010,
    PioVersion::V0
);
instr_test!(
    out(OutDestination::Y, 32),
    0b011_00000_010_00000,
    PioVersion::V0
);

#[test]
#[should_panic(expected = "bit_count must be from 1 to 32")]
fn test_in_bit_width_zero_should_panic() {
    let mut a = Assembler::<32>::new();
    a.r#in(InSource::Y, 0);
    a.assemble_program();
}

#[test]
#[should_panic(expected = "bit_count must be from 1 to 32")]
fn test_in_bit_width_exceeds_max_should_panic() {
    let mut a = Assembler::<32>::new();
    a.r#in(InSource::Y, 33);
    a.assemble_program();
}

#[test]
#[should_panic(expected = "bit_count must be from 1 to 32")]
fn test_out_bit_width_zero_should_panic() {
    let mut a = Assembler::<32>::new();
    a.out(OutDestination::X, 0);
    a.assemble_program();
}

#[test]
#[should_panic(expected = "bit_count must be from 1 to 32")]
fn test_out_bit_width_exceeds_max_should_panic() {
    let mut a = Assembler::<32>::new();
    a.out(OutDestination::X, 33);
    a.assemble_program();
}

instr_test!(push(true, false), 0b100_00000_010_00000, PioVersion::V0);
instr_test!(push(false, true), 0b100_00000_001_00000, PioVersion::V0);

instr_test!(pull(true, false), 0b100_00000_110_00000, PioVersion::V0);
instr_test!(pull(false, true), 0b100_00000_101_00000, PioVersion::V0);

instr_test!(
    mov(
        MovDestination::Y,
        MovOperation::BitReverse,
        MovSource::STATUS
    ),
    0b101_00000_010_10101,
    PioVersion::V0
);

instr_test!(
    irq(true, false, 0b11, IrqIndexMode::DIRECT),
    0b110_00000_010_00_011,
    PioVersion::V0
);
instr_test!(
    irq(false, true, 0b111, IrqIndexMode::REL),
    0b110_00000_001_10_111,
    PioVersion::V0
);
instr_test!(
    irq(true, false, 0b1, IrqIndexMode::PREV),
    0b110_00000_010_01_001,
    PioVersion::V1
);
instr_test!(
    irq(false, true, 0b101, IrqIndexMode::NEXT),
    0b110_00000_001_11_101,
    PioVersion::V1
);

instr_test!(
    set(SetDestination::Y, 10),
    0b111_00000_010_01010,
    PioVersion::V0
);

instr_test!(
    mov(MovDestination::PINDIRS, MovOperation::None, MovSource::X),
    0b101_00000_0110_0001,
    PioVersion::V1
);

instr_test!(
    wait(0, WaitSource::JMPPIN, 0, false),
    0b001_00000_0110_0000,
    PioVersion::V1
);

instr_test!(
    mov_to_rx(MovRxIndex::RXFIFO3),
    0b100_00000_0001_1011,
    PioVersion::V1
);
instr_test!(
    mov_to_rx(MovRxIndex::RXFIFOY),
    0b100_00000_0001_0000,
    PioVersion::V1
);

instr_test!(
    mov_from_rx(MovRxIndex::RXFIFO3),
    0b100_00000_1001_1011,
    PioVersion::V1
);
instr_test!(
    mov_from_rx(MovRxIndex::RXFIFOY),
    0b100_00000_1001_0000,
    PioVersion::V1
);

/// This block ensures that README.md is checked when `cargo test` is run.
#[cfg(doctest)]
mod test_readme {
    macro_rules! external_doc_test {
        ($x:expr) => {
            #[doc = $x]
            extern "C" {}
        };
    }
    external_doc_test!(include_str!("../README.md"));
}

// End of file
