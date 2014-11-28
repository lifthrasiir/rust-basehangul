// Rust-BaseHangul: A binary-to-text encoding with readable Hangul syllables
// Written by Kang Seonghoon
//
// Any copyright is dedicated to the Public Domain.
// https://creativecommons.org/publicdomain/zero/1.0/

//! An implementation of [BaseHangul](https://BaseHangul.github.io) in Rust.

#![feature(if_let)]

extern crate "encoding-index-korean" as encoding_index;

use std::{char, iter};
use std::str::SendStr;

/// The enum that contains either `T` or a decoding error.
pub type DecodeResult<T> = Result<T, SendStr>;

// --------------------&<--------------------
// code to index and vice versa

const NCHARS: u16 = 2350;
const UHC_NCOLS: u16 = 26 + 26 + (0xa1 - 0x81);
const UHC_NROWS: u16 = 0xc7 - 0x81;
const KSX_NCOLS: u16 = 94;
const NCOLS: u16 = 26 + 26 + 126;
const BASE_ROW: u16 = 0xb0 - 0x81;

fn index_to_char(i: u16) -> char {
    debug_assert!(i < NCHARS);
    let row = i / KSX_NCOLS + BASE_ROW;
    let col = i % KSX_NCOLS;
    let code = if row < UHC_NROWS {
        NCOLS * row + (UHC_NCOLS + col)
    } else {
        NCOLS * UHC_NROWS + (row - UHC_NROWS) * KSX_NCOLS + col
    };
    char::from_u32(encoding_index::euc_kr::forward(code) as u32).unwrap()
}

fn char_to_index(c: char) -> Option<u16> {
    let code = encoding_index::euc_kr::backward(c as u32);
    if code < NCOLS * UHC_NROWS {
        let row = code / NCOLS;
        let col = code % NCOLS;
        if row >= BASE_ROW && col >= UHC_NCOLS {
            let index = (row - BASE_ROW) * KSX_NCOLS + (col - UHC_NCOLS);
            debug_assert!(index < NCHARS);
            Some(index)
        } else {
            None
        }
    } else {
        let code = code - NCOLS * UHC_NROWS;
        let row = code / KSX_NCOLS + UHC_NROWS;
        let col = code % KSX_NCOLS;
        let index = (row - BASE_ROW) * KSX_NCOLS + col;
        if index < NCHARS {
            Some(index)
        } else {
            None
        }
    }
}

#[cfg(test)]
#[test]
fn test_index_to_char() {
    assert_eq!(index_to_char(0), '가');
    assert_eq!(index_to_char(1), '각');
    assert_eq!(index_to_char(2), '간');
    assert_eq!(index_to_char(2349), '힝');
}

#[cfg(test)]
#[test]
fn test_char_to_index() {
    assert_eq!(char_to_index('\x00'), None);
    assert_eq!(char_to_index('a'), None);
    assert_eq!(char_to_index('가'), Some(0));
    assert_eq!(char_to_index('각'), Some(1));
    assert_eq!(char_to_index('갂'), None);
    assert_eq!(char_to_index('갃'), None);
    assert_eq!(char_to_index('간'), Some(2));
    assert_eq!(char_to_index('힝'), Some(2349));
    assert_eq!(char_to_index('힣'), None);
    assert_eq!(char_to_index('\uffff'), None);
    assert_eq!(char_to_index('\U0010ffff'), None);
}

#[cfg(test)]
#[test]
fn test_char_to_index_to_char() {
    let mut nextindex = 0;
    for ch in range('가' as u32, '힣' as u32) {
        let ch = char::from_u32(ch).unwrap();
        if let Some(index) = char_to_index(ch) {
            assert_eq!(index, nextindex);
            nextindex += 1;
            assert_eq!(index_to_char(index), ch);
        }
    }
    assert_eq!(nextindex, 2350);
}

// --------------------&<--------------------
// encoder

/// An iterator adapter that packs the byte stream into a stream of unsigned integers < 2,350.
pub struct Packer<Iter> {
    iter: iter::Fuse<Iter>,
    bits: u32, // anything >= 18 bits would work
    nbits: uint,
}

impl<Iter: Iterator<u8>> Packer<Iter> {
    /// Creates a packing adapter.
    pub fn new(iter: Iter) -> Packer<Iter> {
        Packer { iter: iter.fuse(), bits: 0, nbits: 0 }
    }
}

impl<Iter: Iterator<u8>> Iterator<u16> for Packer<Iter> {
    fn next(&mut self) -> Option<u16> {
        loop {
            debug_assert!(self.nbits < 10);
            match self.iter.next() {
                Some(b) => {
                    self.bits = (self.bits << 8) | b as u32;
                    self.nbits += 8;
                    if self.nbits >= 10 {
                        self.nbits -= 10;
                        let code = (self.bits >> self.nbits) & 0x3ff;
                        return Some(code as u16);
                    }
                }
                None if self.nbits > 0 => {
                    // make an 11-bit pattern of 11..1100..00 with nbits+1 zeroes
                    let base = 0x7ff & !((2 << self.nbits) - 1);
                    let code = base | (self.bits & ((1 << self.nbits) - 1));
                    self.bits = 0;
                    self.nbits = 0;
                    return Some(code as u16);
                }
                None => {
                    return None;
                }
            }
        }
    }

    fn size_hint(&self) -> (uint, Option<uint>) {
        // nchars = ceil(nbits / 10)
        let (lo, hi) = self.iter.size_hint();
        ((lo * 8 + 9) / 10, hi.map(|hi| (hi * 8 + 9) / 10))
    }
}

#[cfg(test)]
fn pack(input: &[u8]) -> Vec<u16> {
    Packer::new(input.iter().map(|&v| v)).collect()
}

#[cfg(test)]
#[test]
fn test_pack() {
    assert_eq!(pack(&[]), vec![]);
    assert_eq!(pack(&[0b_____00000000]),
               vec!  [0b1_10_00000000]);
    assert_eq!(pack(&[0b_____11111111]),
               vec!  [0b1_10_11111111]);
    assert_eq!(pack(&[0b00000000, 0b11___________111111]),
               vec!  [0b00000000____11, 0b1_1110_111111]);
    assert_eq!(pack(&[0b11111111, 0b00___________000000]),
               vec!  [0b11111111____00, 0b1_1110_000000]);
    assert_eq!(pack(&[0b00000000, 0b11____111111, 0b0000_____________0000]),
               vec!  [0b00000000____11, 0b111111____0000, 0b1_111110_0000]);
    assert_eq!(pack(&[0b11111111, 0b00____000000, 0b1111_____________1111]),
               vec!  [0b11111111____00, 0b000000____1111, 0b1_111110_1111]);
    assert_eq!(pack(&[0b00000000, 0b11____111111, 0b0000____0000, 0b111111_______________11]),
               vec!  [0b00000000____11, 0b111111____0000, 0b0000____111111, 0b1_11111110_11]);
    assert_eq!(pack(&[0b11111111, 0b00____000000, 0b1111____1111, 0b000000_______________00]),
               vec!  [0b11111111____00, 0b000000____1111, 0b1111____000000, 0b1_11111110_00]);
    assert_eq!(pack(&[0b00000000, 0b11____111111, 0b0000____0000, 0b111111____11, 0b00000000]),
               vec!  [0b00000000____11, 0b111111____0000, 0b0000____111111, 0b11____00000000]);

    // spec examples&
    assert_eq!(pack(&[49, 50, 51, 97, 98]), vec![196, 803, 216, 354]);
    assert_eq!(pack(&[49, 50, 51, 100]), vec![196, 803, 217, 2040]);
    assert_eq!(pack(&[49]), vec![1585]);
}

/// An iterator adapter that encodes the byte stream into the BaseHangul stream.
pub struct Encoder<Iter> {
    packer: Packer<Iter>,
}

impl<Iter: Iterator<u8>> Encoder<Iter> {
    /// Creates an encoding adapter.
    pub fn new(iter: Iter) -> Encoder<Iter> {
        Encoder { packer: Packer::new(iter) }
    }
}

impl<Iter: Iterator<u8>> Iterator<char> for Encoder<Iter> {
    fn next(&mut self) -> Option<char> { self.packer.next().map(index_to_char) }
    fn size_hint(&self) -> (uint, Option<uint>) { self.packer.size_hint() }
}

/// Converts a byte sequence into the BaseHangul string.
pub fn encode(input: &[u8]) -> String {
    Encoder::new(input.iter().map(|&v| v)).collect()
}

#[cfg(test)]
#[test]
fn test_encode() {
    // spec examples
    assert_eq!(encode(&[49, 50, 51, 97, 98]), "꺽먹꼍녜".to_string());
    assert_eq!(encode(&[49, 50, 51, 100]), "꺽먹꼐톈".to_string());
    assert_eq!(encode(&[49]), "쟌".to_string());
    assert_eq!(encode(&[]), "".to_string());
}

// --------------------&<--------------------
// decoder

/// An iterator adapter that unpacks the byte stream from a stream of unsigned integers < 2,350.
pub struct Unpacker<Iter> {
    iter: Iter,
    bits: u32,
    nbits: uint,
    last: bool,
}

impl<Iter: Iterator<u16>> Unpacker<Iter> {
    /// Creates an unpacking adapter.
    pub fn new(iter: Iter) -> Unpacker<Iter> {
        Unpacker { iter: iter, bits: 0, nbits: 0, last: false }
    }
}

impl<Iter: Iterator<u16>> Iterator<DecodeResult<u8>> for Unpacker<Iter> {
    fn next(&mut self) -> Option<DecodeResult<u8>> {
        loop {
            // emit the buffered byte
            if self.nbits >= 8 {
                self.nbits -= 8;
                let code = (self.bits >> self.nbits) & 0xff;
                return Some(Ok(code as u8));
            }

            // if we have no more than 8 bits, we are almost done
            if self.last {
                if self.nbits > 0 {
                    self.nbits = 0;
                    return Some(Err("non-integral number of bytes".into_cow()));
                } else {
                    return None;
                }
            }

            match self.iter.next() {
                Some(b @ 0...1023) => {
                    self.bits = (self.bits << 10) | b as u32;
                    self.nbits += 10;
                }
                Some(b @ 1024...2045) => {
                    static CL1: [u8, ..32] = [0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,
                                              1,1,1,1,1,1,1,1, 2,2,2,2,3,3,4,5];
                    let mut nones = CL1[((b >> 5) & 0x1f) as uint] as uint;
                    if nones == 5 { // we may have more ones in the lower half
                        nones += CL1[(b & 0x1f) as uint] as uint;
                    }
                    debug_assert!(nones < 10);
                    let nbits = 9 - nones;

                    self.last = true;
                    self.bits = (self.bits << nbits) | (b as u32 & ((1 << nbits) - 1));
                    self.nbits += nbits;
                }
                Some(_) => {
                    self.last = true;
                    self.nbits = 0;
                    return Some(Err("invalid code word".into_cow()));
                }
                None => {
                    self.last = true;
                }
            }
        }
    }

    fn size_hint(&self) -> (uint, Option<uint>) {
        // nchars * 10 - 9 <= nbits <= nchars * 10
        let (lo, hi) = self.iter.size_hint();
        ((lo * 10 - 9 + 7) / 8, hi.map(|hi| (hi * 10 + 7) / 8))
    }
}

#[cfg(test)]
fn unpack(input: &[u16]) -> DecodeResult<Vec<u8>> {
    Unpacker::new(input.iter().map(|&v| v)).collect()
}

#[cfg(test)]
#[test]
fn test_unpack() {
    assert_eq!(unpack(&[]), Ok(vec![]));
    assert_eq!(unpack(&[0b1_10_00000000]),
               Ok(vec! [0b_____00000000]));
    assert_eq!(unpack(&[0b1_10_11111111]),
               Ok(vec! [0b_____11111111]));
    assert_eq!(unpack(&[0b00000000____11, 0b1_1110_111111]),
               Ok(vec! [0b00000000, 0b11___________111111]));
    assert_eq!(unpack(&[0b11111111____00, 0b1_1110_000000]),
               Ok(vec! [0b11111111, 0b00___________000000]));
    assert_eq!(unpack(&[0b00000000____11, 0b111111____0000, 0b1_111110_0000]),
               Ok(vec! [0b00000000, 0b11____111111, 0b0000_____________0000]));
    assert_eq!(unpack(&[0b11111111____00, 0b000000____1111, 0b1_111110_1111]),
               Ok(vec! [0b11111111, 0b00____000000, 0b1111_____________1111]));
    assert_eq!(unpack(&[0b00000000____11, 0b111111____0000, 0b0000____111111, 0b1_11111110_11]),
               Ok(vec! [0b00000000, 0b11____111111, 0b0000____0000, 0b111111_______________11]));
    assert_eq!(unpack(&[0b11111111____00, 0b000000____1111, 0b1111____000000, 0b1_11111110_00]),
               Ok(vec! [0b11111111, 0b00____000000, 0b1111____1111, 0b000000_______________00]));
    assert_eq!(unpack(&[0b00000000____11, 0b111111____0000, 0b0000____111111, 0b11____00000000]),
               Ok(vec! [0b00000000, 0b11____111111, 0b0000____0000, 0b111111____11, 0b00000000]));

    // spec examples
    assert_eq!(unpack(&[196, 803, 216, 354]), Ok(vec![49, 50, 51, 97, 98]));
    assert_eq!(unpack(&[196, 803, 217, 2040]), Ok(vec![49, 50, 51, 100]));
    assert_eq!(unpack(&[1585]), Ok(vec![49]));

    // error: non-integral number of bits
    assert!(unpack(&[0b1_111111110_0]).is_err());
    assert!(unpack(&[0b1_11111110_00]).is_err());
    assert!(unpack(&[0b1_1111110_000]).is_err());
    assert!(unpack(&[0b1_111110_0000]).is_err());
    assert!(unpack(&[0b1_11110_00000]).is_err());
    assert!(unpack(&[0b1_1110_000000]).is_err());
    assert!(unpack(&[0b1_110_0000000]).is_err());
    assert!(unpack(&[0b1_0_000000000]).is_err());
    assert!(unpack(&[1]).is_err());
    assert!(unpack(&[1, 0b1_111111110_0]).is_err());
    assert!(unpack(&[1, 0b1_11111110_00]).is_err());
    assert!(unpack(&[1, 0b1_1111110_000]).is_err());
    assert!(unpack(&[1, 0b1_111110_0000]).is_err());
    assert!(unpack(&[1, 0b1_11110_00000]).is_err());
    assert!(unpack(&[1, 0b1_110_0000000]).is_err());
    assert!(unpack(&[1, 0b1_10_00000000]).is_err());
    assert!(unpack(&[1, 0b1_0_000000000]).is_err());
    assert!(unpack(&[1, 2]).is_err());
    assert!(unpack(&[1, 2, 0b1_111111110_0]).is_err());
    assert!(unpack(&[1, 2, 0b1_11111110_00]).is_err());
    assert!(unpack(&[1, 2, 0b1_1111110_000]).is_err());
    assert!(unpack(&[1, 2, 0b1_11110_00000]).is_err());
    assert!(unpack(&[1, 2, 0b1_1110_000000]).is_err());
    assert!(unpack(&[1, 2, 0b1_110_0000000]).is_err());
    assert!(unpack(&[1, 2, 0b1_10_00000000]).is_err());
    assert!(unpack(&[1, 2, 0b1_0_000000000]).is_err());
    assert!(unpack(&[1, 2, 3]).is_err());
    assert!(unpack(&[1, 2, 3, 0b1_111111110_0]).is_err());
    assert!(unpack(&[1, 2, 3, 0b1_1111110_000]).is_err());
    assert!(unpack(&[1, 2, 3, 0b1_111110_0000]).is_err());
    assert!(unpack(&[1, 2, 3, 0b1_11110_00000]).is_err());
    assert!(unpack(&[1, 2, 3, 0b1_1110_000000]).is_err());
    assert!(unpack(&[1, 2, 3, 0b1_110_0000000]).is_err());
    assert!(unpack(&[1, 2, 3, 0b1_10_00000000]).is_err());
    assert!(unpack(&[1, 2, 3, 0b1_0_000000000]).is_err());

    // error: invalid code word
    assert!(unpack(&[0b1_1111111110]).is_err());
    assert!(unpack(&[0b1_1111111111]).is_err());
    assert!(unpack(&[2048]).is_err());
    assert!(unpack(&[2349]).is_err());
}

/// An iterator adapter that decodes the byte stream from the BaseHangul stream.
pub struct Decoder<Iter> {
    unpacker: Unpacker<iter::Map<'static, char, u16, Iter>>,
}

impl<Iter: Iterator<char>> Decoder<Iter> {
    /// Creates a decoding adapter.
    pub fn new(iter: Iter) -> Decoder<Iter> {
        fn char_to_index_or_so(c: char) -> u16 {
            char_to_index(c).unwrap_or(NCHARS /*out-of-bounds*/)
        }
        Decoder { unpacker: Unpacker::new(iter.map(char_to_index_or_so)) }
    }
}

impl<Iter: Iterator<char>> Iterator<DecodeResult<u8>> for Decoder<Iter> {
    fn next(&mut self) -> Option<DecodeResult<u8>> {
        self.unpacker.next()
    }
    fn size_hint(&self) -> (uint, Option<uint>) {
        let (lo, hi) = self.unpacker.size_hint();
        (if lo > 0 {1} else {0}, hi) // error can occur anywhere
    }
}

/// Converts a BaseHangul string into the byte sequence if possible.
pub fn decode(input: &str) -> DecodeResult<Vec<u8>> {
    Decoder::new(input.chars().filter(|c| !c.is_whitespace())).collect()
}

#[cfg(test)]
#[test]
fn test_decode() {
    // spec examples
    assert_eq!(decode("꺽먹꼍녜"), Ok(vec![49, 50, 51, 97, 98]));
    assert_eq!(decode("꺽먹꼐톈"), Ok(vec![49, 50, 51, 100]));
    assert_eq!(decode("쟌"), Ok(vec![49]));
    assert_eq!(decode(""), Ok(vec![]));

    // ignores whitespace
    assert_eq!(decode("   쟌    "), Ok(vec![49]));
    assert_eq!(decode("\t가\n가\u3000가가"), Ok(vec![0, 0, 0, 0, 0]));

    // error: invalid
    assert!(decode("X").is_err());
    assert!(decode("뷁").is_err()); // not in KS X 1001
    assert!(decode("힝").is_err()); // out of bounds
}

