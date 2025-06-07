use std::ops::BitXorAssign;

use crate::linear::TruthTable;
use crate::linear::XorAnds;

#[derive(Debug, Clone)]
pub struct U8ANFs {
    pub truth_tables: [TruthTable; u8::BITS as usize],
    pub anf: [XorAnds; u8::BITS as usize],
}

impl U8ANFs {
    fn get_xor_ands(truth_tables: &[TruthTable; u8::BITS as usize]) -> [XorAnds; u8::BITS as usize] {
        truth_tables.each_ref().map(|tt| XorAnds::from_truth_table(8, tt.clone()))
    }

    pub fn from_bytes(mut f: impl FnMut(u8) -> u8) -> Self {
        let truth_tables = std::array::from_fn(|index| {
            TruthTable::from_assignments(8, |assignment| {
                f(assignment as u8) & (1 << index) != 0
            })
        });
        U8ANFs {
            anf: Self::get_xor_ands(&truth_tables),
            truth_tables,
        }
    }

    pub fn id() -> Self {
        Self::from_bytes(std::convert::identity)
    }

    pub fn compose_right(&mut self, mut g: impl FnMut(u8) -> u8) {
        for assignment in 0..=u8::MAX as usize {
            let mut bits = 0;
            for bit in (0..u8::BITS as usize).rev() {
                let result = *self.truth_tables[bit].bit_rep.get(assignment).unwrap() as u8;
                bits |= result << bit;
            }
            let result = g(bits);
            for bit in 0..u8::BITS as usize {
                self.truth_tables[bit].bit_rep.set(assignment, (result >> bit) & 0b1 != 0);
            }
        }
        self.anf = Self::get_xor_ands(&self.truth_tables);
    }

    pub fn gmul(mut x: u8, mut y: u8) -> u8 {
        let mut p = 0;
        for _ in 0..8 {
            if (y & 0b1) != 0 {
                p ^= x;
            }
            let high_bit = x & 0b1000_0000 != 0;
            x = x.wrapping_shl(1);
            if high_bit {
                x ^= 0x1B;
            }
            y >>= 1;
        }
        p
    }

    pub fn x_times(n: u8) -> Self {
        Self::from_bytes(|assignment| Self::gmul(assignment as u8, n))
    }

    pub fn sbox() -> Self {
        Self::from_bytes(sbox)
    }

    pub fn sbox_times(n: u8) -> Self {
        Self::from_bytes(|assignment| Self::gmul(sbox(assignment), n))
    }

    pub fn inverse_sbox() -> Self {
        Self::from_bytes(inverse_sbox)
    }

    pub fn times_inverse_sbox(n: u8) -> Self {
        Self::from_bytes(|assignment| inverse_sbox(Self::gmul(assignment, n)))
    }

    pub fn zero() -> Self {
        U8ANFs::default()
    }
}

fn sbox(byte: u8) -> u8 {
    static SBOX: [u8; 256] = [
        0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B, 0xFE, 0xD7, 0xAB, 0x76,
        0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0, 0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0,
        0xB7, 0xFD, 0x93, 0x26, 0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15,
        0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2, 0xEB, 0x27, 0xB2, 0x75,
        0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0, 0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84,
        0x53, 0xD1, 0x00, 0xED, 0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF,
        0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F, 0x50, 0x3C, 0x9F, 0xA8,
        0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5, 0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2,
        0xCD, 0x0C, 0x13, 0xEC, 0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73,
        0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14, 0xDE, 0x5E, 0x0B, 0xDB,
        0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C, 0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79,
        0xE7, 0xC8, 0x37, 0x6D, 0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08,
        0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F, 0x4B, 0xBD, 0x8B, 0x8A,
        0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E, 0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E,
        0xE1, 0xF8, 0x98, 0x11, 0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF,
        0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F, 0xB0, 0x54, 0xBB, 0x16,
    ];
    SBOX[byte as usize]
}

fn inverse_sbox(byte: u8) -> u8 {
    static INV_SBOX: [u8; 256] = [
        0x52, 0x09, 0x6A, 0xD5, 0x30, 0x36, 0xA5, 0x38, 0xBF, 0x40, 0xA3, 0x9E, 0x81, 0xF3, 0xD7, 0xFB,
        0x7C, 0xE3, 0x39, 0x82, 0x9B, 0x2F, 0xFF, 0x87, 0x34, 0x8E, 0x43, 0x44, 0xC4, 0xDE, 0xE9, 0xCB,
        0x54, 0x7B, 0x94, 0x32, 0xA6, 0xC2, 0x23, 0x3D, 0xEE, 0x4C, 0x95, 0x0B, 0x42, 0xFA, 0xC3, 0x4E,
        0x08, 0x2E, 0xA1, 0x66, 0x28, 0xD9, 0x24, 0xB2, 0x76, 0x5B, 0xA2, 0x49, 0x6D, 0x8B, 0xD1, 0x25,
        0x72, 0xF8, 0xF6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xD4, 0xA4, 0x5C, 0xCC, 0x5D, 0x65, 0xB6, 0x92,
        0x6C, 0x70, 0x48, 0x50, 0xFD, 0xED, 0xB9, 0xDA, 0x5E, 0x15, 0x46, 0x57, 0xA7, 0x8D, 0x9D, 0x84,
        0x90, 0xD8, 0xAB, 0x00, 0x8C, 0xBC, 0xD3, 0x0A, 0xF7, 0xE4, 0x58, 0x05, 0xB8, 0xB3, 0x45, 0x06,
        0xD0, 0x2C, 0x1E, 0x8F, 0xCA, 0x3F, 0x0F, 0x02, 0xC1, 0xAF, 0xBD, 0x03, 0x01, 0x13, 0x8A, 0x6B,
        0x3A, 0x91, 0x11, 0x41, 0x4F, 0x67, 0xDC, 0xEA, 0x97, 0xF2, 0xCF, 0xCE, 0xF0, 0xB4, 0xE6, 0x73,
        0x96, 0xAC, 0x74, 0x22, 0xE7, 0xAD, 0x35, 0x85, 0xE2, 0xF9, 0x37, 0xE8, 0x1C, 0x75, 0xDF, 0x6E,
        0x47, 0xF1, 0x1A, 0x71, 0x1D, 0x29, 0xC5, 0x89, 0x6F, 0xB7, 0x62, 0x0E, 0xAA, 0x18, 0xBE, 0x1B,
        0xFC, 0x56, 0x3E, 0x4B, 0xC6, 0xD2, 0x79, 0x20, 0x9A, 0xDB, 0xC0, 0xFE, 0x78, 0xCD, 0x5A, 0xF4,
        0x1F, 0xDD, 0xA8, 0x33, 0x88, 0x07, 0xC7, 0x31, 0xB1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xEC, 0x5F,
        0x60, 0x51, 0x7F, 0xA9, 0x19, 0xB5, 0x4A, 0x0D, 0x2D, 0xE5, 0x7A, 0x9F, 0x93, 0xC9, 0x9C, 0xEF,
        0xA0, 0xE0, 0x3B, 0x4D, 0xAE, 0x2A, 0xF5, 0xB0, 0xC8, 0xEB, 0xBB, 0x3C, 0x83, 0x53, 0x99, 0x61,
        0x17, 0x2B, 0x04, 0x7E, 0xBA, 0x77, 0xD6, 0x26, 0xE1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0C, 0x7D,
    ];
    INV_SBOX[byte as usize]
}

impl std::fmt::Display for U8ANFs {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for (bit, anf) in self.anf.iter().enumerate() {
            writeln!(f, "bit {bit}: {anf}")?;
        }
        Ok(())
    }
}

impl Default for U8ANFs {
    fn default() -> Self {
        U8ANFs {
            truth_tables: std::array::from_fn(|_| TruthTable::zeros(u8::BITS as usize)),
            anf: std::array::from_fn(|_| XorAnds::zeros(u8::BITS as usize)),
        }
    }
}

impl BitXorAssign<&U8ANFs> for U8ANFs {
    fn bitxor_assign(&mut self, rhs: &Self) {
        for (lhs, rhs) in self.truth_tables.iter_mut().zip(rhs.truth_tables.iter()) {
            *lhs ^= rhs;
        }
        for (lhs, rhs) in self.anf.iter_mut().zip(rhs.anf.iter()) {
            *lhs ^= rhs;
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct U32ANFs {
    pub bytes: [U8ANFs; (u32::BITS / u8::BITS) as usize],
}

impl U32ANFs {
    fn rotate_bytes(&mut self) {
        self.bytes.rotate_right(1);
    }

    fn unrotate_bytes(&mut self) {
        self.bytes.rotate_left(1);
    }

    pub fn sbox_bytes(&mut self) {
        for byte in self.bytes.iter_mut() {
            byte.compose_right(sbox);
        }
    }

    fn inverse_sbox_bytes(&mut self) {
        for byte in self.bytes.iter_mut() {
            byte.compose_right(inverse_sbox);
        }
    }

    pub fn rotate_sbox_xor(&mut self, rhs: u8) {
        self.rotate_bytes();
        let mut bytes = self.bytes.iter_mut();
        let first_byte = bytes.next().unwrap();
        first_byte.compose_right(|assignment| sbox(assignment) ^ rhs);
        for byte in self.bytes.iter_mut() {
            byte.compose_right(sbox);
        }
    }

    fn inverse_rotate_sbox_xor(&mut self, rhs: u8) {
        let mut bytes = self.bytes.iter_mut();
        let first_byte = bytes.next().unwrap();
        first_byte.compose_right(|assignment| inverse_sbox(assignment ^ rhs));
        for byte in self.bytes.iter_mut() {
            byte.compose_right(inverse_sbox);
        }
        self.unrotate_bytes();
    }

    fn id() -> Self {
        let id = U8ANFs::id();
        U32ANFs {
            bytes: std::array::from_fn(|_| id.clone()),
        }
    }
}

impl BitXorAssign<&U32ANFs> for U32ANFs {
    fn bitxor_assign(&mut self, rhs: &Self) {
        for (lhs, rhs) in self.bytes.iter_mut().zip(rhs.bytes.iter()) {
            *lhs ^= rhs;
        }
    }
}

const ORIGINAL_KEY_WORDS: usize = 8;

#[derive(Debug)]
pub struct OriginalKey {
    pub words: Box<[U32ANFs; ORIGINAL_KEY_WORDS]>,
}

impl Default for OriginalKey {
    fn default() -> Self {
        OriginalKey {
            words: Box::new(std::array::from_fn(|_| U32ANFs::id())),
        }
    }
}

const RCONS: [u8; 10] = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36];
const ROUNDS: usize = 15;

#[derive(Debug, Default, Clone)]
pub struct RoundKey {
    pub expanded: Box<[U32ANFs; 4]>
}

#[derive(Debug)]
pub struct KeySchedule {
    pub rounds: [RoundKey; ROUNDS],
}

impl KeySchedule {
    pub fn from_original_key(original: OriginalKey) -> Self {
        fn step_to_round_word(step: usize) -> (usize, usize) {
            (step / 4, step % 4)
        }

        let mut rounds = <[RoundKey; ROUNDS]>::default();
        for (step, original_word) in original.words.into_iter().enumerate() {
            let (round, expanded_word) = step_to_round_word(step);
            rounds[round].expanded[expanded_word] = original_word;
        }
        let (mut last_round, mut last_expanded_word) = step_to_round_word(ORIGINAL_KEY_WORDS - 1);
        for step in ORIGINAL_KEY_WORDS..ROUNDS * 4 {
            let mut last_word_anfs = rounds[last_round].expanded[last_expanded_word].clone();
            let (new_round, new_expanded_word) = step_to_round_word(step);
            let (old_round, old_expanded_word) = step_to_round_word(step - ORIGINAL_KEY_WORDS);
            match step % ORIGINAL_KEY_WORDS {
                0 => last_word_anfs.rotate_sbox_xor(RCONS[step / ORIGINAL_KEY_WORDS]),
                4 if ORIGINAL_KEY_WORDS > 6 => last_word_anfs.sbox_bytes(),
                _ => (),
            }
            last_word_anfs ^= &rounds[old_round].expanded[old_expanded_word];
            rounds[new_round].expanded[new_expanded_word] = last_word_anfs;
            (last_round, last_expanded_word) = (new_round, new_expanded_word);
        }
        KeySchedule {
            rounds,
        }
    }

    pub fn from_any_key() -> Self {
        KeySchedule::from_original_key(Default::default())
    }
}

#[derive(Debug, Default, Clone)]
pub struct Block {
    pub columns: Box<[U32ANFs; 4]>,
}

impl Block {
    fn sub_bytes(&mut self) {
        for column in self.columns.iter_mut() {
            column.sbox_bytes();
        }
    }

    fn transpose(&mut self) {
        for col in 0..4 {
            for row in (col + 1)..4 {
                let [col1, col2] = self.columns.get_disjoint_mut([col, row]).unwrap();
                std::mem::swap(&mut col1.bytes[row], &mut col2.bytes[col]);
            }
        }
    }

    fn shift_cols(&mut self) {
        for (shift, col) in self.columns.iter_mut().enumerate() {
            for _ in 0..shift {
                col.rotate_bytes();
            }
        }
    }

    #[must_use]
    fn as_mixed_rows(&self) -> Self {
        let mut mixed_columns = Block::default();
        for (c, out_column) in mixed_columns.columns.iter_mut().enumerate() {
            let mut constants = [2, 3, 1, 1];
            for (r, out_byte) in out_column.bytes.iter_mut().enumerate() {
                for (mut in_byte, c) in self.columns[c].bytes.iter().cloned().zip(constants) {
                    in_byte.compose_right(|n| U8ANFs::gmul(n, c));
                    *out_byte ^= &in_byte;
                }
                if r < 3 {
                    constants.rotate_right(1);
                }
            }
        }
        mixed_columns
    }

    fn mix_rows(&mut self) {
        *self = self.as_mixed_rows();
    }

    pub fn id() -> Self {
        Block {
            columns: Box::new(std::array::from_fn(|_| U32ANFs::id())),
        }
    }

    pub fn encrypt(&mut self, schedule: &KeySchedule) {
        *self ^= &schedule.rounds[0];
        for round_key in &schedule.rounds[1..ROUNDS - 1] {
            self.sub_bytes();
            self.transpose();
            self.shift_cols();
            self.mix_rows();
            self.transpose();
            *self ^= round_key;
        }
        self.sub_bytes();
        self.transpose();
        self.shift_cols();
        self.transpose();
        *self ^= &schedule.rounds[ROUNDS - 1];
    }
}

impl BitXorAssign<&RoundKey> for Block {
    fn bitxor_assign(&mut self, rhs: &RoundKey) {
        for (column, expanded) in self.columns.iter_mut().zip(rhs.expanded.iter()) {
            *column ^= expanded;
        }
    }
}
