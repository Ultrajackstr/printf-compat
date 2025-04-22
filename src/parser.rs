use core::ffi::*;

use crate::{Argument, DoubleFormat, Flags, SignedInt, Specifier, UnsignedInt};
use itertools::Itertools;

fn next_char(sub: &[u8]) -> &[u8] {
    sub.get(1..).unwrap_or(&[])
}

/// Parse the [Flags field](https://en.wikipedia.org/wiki/Printf_format_string#Flags_field).
fn parse_flags(mut sub: &[u8]) -> (Flags, &[u8]) {
    let mut flags: Flags = Flags::empty();
    while let Some(&ch) = sub.first() {
        flags.insert(match ch {
            b'-' => Flags::LEFT_ALIGN,
            b'+' => Flags::PREPEND_PLUS,
            b' ' => Flags::PREPEND_SPACE,
            b'0' => Flags::PREPEND_ZERO,
            b'\'' => Flags::THOUSANDS_GROUPING,
            b'#' => Flags::ALTERNATE_FORM,
            _ => break,
        });
        sub = next_char(sub)
    }
    (flags, sub)
}

/// Parse the [Width field](https://en.wikipedia.org/wiki/Printf_format_string#Width_field).
unsafe fn parse_width<'a>(mut sub: &'a [u8], args: &mut VaList) -> (c_int, &'a [u8]) {
    let mut width: c_int = 0;
    if sub.first() == Some(&b'*') {
        return (unsafe { args.arg() }, next_char(sub));
    }
    while let Some(&ch) = sub.first() {
        match ch {
            // https://rust-malaysia.github.io/code/2020/07/11/faster-integer-parsing.html#the-bytes-solution
            b'0'..=b'9' => width = width * 10 + (ch & 0x0f) as c_int,
            _ => break,
        }
        sub = next_char(sub);
    }
    (width, sub)
}

/// Parse the [Precision field](https://en.wikipedia.org/wiki/Printf_format_string#Precision_field).
unsafe fn parse_precision<'a>(sub: &'a [u8], args: &mut VaList) -> (Option<c_int>, &'a [u8]) {
    match sub.first() {
        Some(&b'.') => {
            let (prec, sub) = unsafe { parse_width(next_char(sub), args) };
            (Some(prec), sub)
        }
        _ => (None, sub),
    }
}

#[derive(Debug, Copy, Clone)]
enum Length {
    Int,
    /// `hh`
    Char,
    /// `h`
    Short,
    /// `l`
    Long,
    /// `ll`
    LongLong,
    /// `z`
    Usize,
    /// `t`
    Isize,
}

impl Length {
    unsafe fn parse_signed(self, args: &mut VaList) -> SignedInt {
        match self {
            Length::Int => SignedInt::Int(unsafe { args.arg() }),
            Length::Char => SignedInt::Char(unsafe { args.arg() }),
            Length::Short => SignedInt::Short(unsafe { args.arg() }),
            Length::Long => SignedInt::Long(unsafe { args.arg() }),
            Length::LongLong => SignedInt::LongLong(unsafe { args.arg() }),
            // for some reason, these exist as different options, yet produce the same output
            Length::Usize | Length::Isize => SignedInt::Isize(unsafe { args.arg() }),
        }
    }
    unsafe fn parse_unsigned(self, args: &mut VaList) -> UnsignedInt {
        match self {
            Length::Int => UnsignedInt::Int(unsafe { args.arg() }),
            Length::Char => UnsignedInt::Char(unsafe { args.arg() }),
            Length::Short => UnsignedInt::Short(unsafe { args.arg() }),
            Length::Long => UnsignedInt::Long(unsafe { args.arg() }),
            Length::LongLong => UnsignedInt::LongLong(unsafe { args.arg() }),
            // for some reason, these exist as different options, yet produce the same output
            Length::Usize | Length::Isize => UnsignedInt::Isize(unsafe { args.arg() }),
        }
    }
}

/// Parse the [Length field](https://en.wikipedia.org/wiki/Printf_format_string#Length_field).
fn parse_length(sub: &[u8]) -> (Length, &[u8]) {
    match sub.first().copied() {
        Some(b'h') => match sub.get(1).copied() {
            Some(b'h') => (Length::Char, sub.get(2..).unwrap_or(&[])),
            _ => (Length::Short, next_char(sub)),
        },
        Some(b'l') => match sub.get(1).copied() {
            Some(b'l') => (Length::LongLong, sub.get(2..).unwrap_or(&[])),
            _ => (Length::Long, next_char(sub)),
        },
        Some(b'z') => (Length::Usize, next_char(sub)),
        Some(b't') => (Length::Isize, next_char(sub)),
        _ => (Length::Int, sub),
    }
}

/// Parse a format parameter and write it somewhere.
///
/// # Safety
///
/// [`VaList`]s are *very* unsafe. The passed `format` and `args` parameter must be a valid [`printf` format string](http://www.cplusplus.com/reference/cstdio/printf/).
pub unsafe fn format(
    format: *const c_char,
    mut args: VaList,
    mut handler: impl FnMut(Argument) -> c_int,
) -> c_int {
    let str = unsafe { CStr::from_ptr(format).to_bytes() };
    let mut iter = str.split(|&c| c == b'%');
    let mut written = 0;

    macro_rules! err {
        ($ex: expr) => {{
            let res = $ex;
            if res < 0 {
                return -1;
            } else {
                written += res;
            }
        }};
    }
    if let Some(begin) = iter.next() {
        err!(handler(Specifier::Bytes(begin).into()));
    }
    let mut last_was_percent = false;
    for (sub, next) in iter.map(Some).chain(core::iter::once(None)).tuple_windows() {
        let sub = match sub {
            Some(sub) => sub,
            None => break,
        };
        if last_was_percent {
            err!(handler(Specifier::Bytes(sub).into()));
            last_was_percent = false;
            continue;
        }
        let (flags, sub) = parse_flags(sub);
        let (width, sub) = unsafe { parse_width(sub, &mut args) };
        let (precision, sub) = unsafe { parse_precision(sub, &mut args) };
        let (length, sub) = parse_length(sub);
        let ch = sub
            .first()
            .unwrap_or(if next.is_some() { &b'%' } else { &0 });
        err!(handler(Argument {
            flags,
            width,
            precision,
            specifier: match ch {
                b'%' => {
                    last_was_percent = true;
                    Specifier::Percent
                }
                b'd' | b'i' => Specifier::Int(unsafe { length.parse_signed(&mut args) }),
                b'x' => Specifier::Hex(unsafe { length.parse_unsigned(&mut args) }),
                b'X' => Specifier::UpperHex(unsafe { length.parse_unsigned(&mut args) }),
                b'u' => Specifier::Uint(unsafe { length.parse_unsigned(&mut args) }),
                b'o' => Specifier::Octal(unsafe { length.parse_unsigned(&mut args) }),
                b'f' | b'F' => Specifier::Double {
                    value: unsafe { args.arg() },
                    format: DoubleFormat::Normal.set_upper(ch.is_ascii_uppercase()),
                },
                b'e' | b'E' => Specifier::Double {
                    value: unsafe { args.arg() },
                    format: DoubleFormat::Scientific.set_upper(ch.is_ascii_uppercase()),
                },
                b'g' | b'G' => Specifier::Double {
                    value: unsafe { args.arg() },
                    format: DoubleFormat::Auto.set_upper(ch.is_ascii_uppercase()),
                },
                b'a' | b'A' => Specifier::Double {
                    value: unsafe { args.arg() },
                    format: DoubleFormat::Hex.set_upper(ch.is_ascii_uppercase()),
                },
                b's' => {
                    let arg: *mut c_char = unsafe { args.arg() };
                    // As a common extension supported by glibc, musl, and
                    // others, format a NULL pointer as "(null)".
                    if arg.is_null() {
                        Specifier::Bytes(b"(null)")
                    }
                    // Heuristic: Check for suspiciously low addresses (e.g., < page size)
                    // which often indicate an integer passed instead of a pointer.
                    else if (arg as usize) < 4096 {
                        Specifier::Bytes(b"(invalid_ptr)") // Prevent panic on likely invalid pointers
                    } else {
                        // Pointer seems plausible, but might not be null-terminated
                        // or could point to invalid memory further along.
                        // Search for null terminator within a reasonable bound.
                        const MAX_STRING_LEN: usize = 1024; // Define a safety limit
                        let mut len = 0;
                        let mut found_null = false;
                        while len < MAX_STRING_LEN {
                            // SAFETY: Dereferencing `arg.add(len)` is unsafe if `arg`
                            // points to invalid/unmapped memory or memory shorter than `len`.
                            // This bounded loop mitigates reading indefinitely, but the
                            // initial dereferences can still cause UB if `arg` is fundamentally invalid.
                            // This is inherent when dealing with potentially invalid C pointers.
                            let byte = unsafe { *arg.add(len) };
                            if byte == 0 {
                                found_null = true;
                                break;
                            }
                            len += 1;
                        }

                        if found_null {
                            // Found null within bounds. Create a slice including the null terminator.
                            // SAFETY: We've checked bytes up to `len` and found a null at `len`.
                            // `from_raw_parts` requires the memory to be valid for reads of `len + 1` bytes.
                            let slice_with_nul =
                                unsafe { core::slice::from_raw_parts(arg as *const u8, len + 1) };
                            // `from_bytes_with_nul` checks for interior nulls and returns a Result.
                            match CStr::from_bytes_with_nul(slice_with_nul) {
                                Ok(cstr) => Specifier::String(cstr), // Success
                                Err(_) => Specifier::Bytes(b"(invalid_c_str_sequence)"), // Should be rare if loop worked
                            }
                        } else {
                            // No null terminator found within MAX_STRING_LEN.
                            Specifier::Bytes(b"(string_too_long_or_unterminated)")
                        }
                    }
                }
                b'c' => Specifier::Char(unsafe { args.arg() }),
                b'p' => Specifier::Pointer(unsafe { args.arg() }),
                b'n' => Specifier::WriteBytesWritten(written, unsafe { args.arg() }),
                _ => return -1,
            },
        }));
        err!(handler(Specifier::Bytes(next_char(sub)).into()));
    }
    written
}
