pub type RoundKey = crate::block::Block;

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

#[derive(Debug)]
pub struct KeySchedule {
    pub rounds: [RoundKey; KeySchedule::ROUND_KEYS],
}

impl KeySchedule {
    pub const ROUND_KEYS: usize = 15;
    pub const ROUND_CONSTANTS: [u8; 10] = [
        0x01, 0x02, 0x04, 0x08, 0x10,
        0x20, 0x40, 0x80, 0x1B, 0x36,
    ];

    pub fn from_original_key(original: OriginalKey) -> Self {
        fn step_to_round_word(step: usize) -> (usize, usize) {
            (step / 4, step % 4)
        }

        let mut rounds = <[RoundKey; Self::ROUND_KEYS]>::default();
        for (step, original_word) in original.words.into_iter().enumerate() {
            let (round, expanded_word) = step_to_round_word(step);
            rounds[round].columns[expanded_word] = original_word;
        }
        let (mut last_round, mut last_expanded_word) = step_to_round_word(ORIGINAL_KEY_WORDS - 1);
        for step in ORIGINAL_KEY_WORDS..Self::ROUND_KEYS * 4 {
            let mut last_word_anfs = rounds[last_round].columns[last_expanded_word].clone();
            let (new_round, new_expanded_word) = step_to_round_word(step);
            let (old_round, old_expanded_word) = step_to_round_word(step - ORIGINAL_KEY_WORDS);
            match step % ORIGINAL_KEY_WORDS {
                0 => last_word_anfs.rotate_sbox_xor(
                    Self::ROUND_CONSTANTS[step / ORIGINAL_KEY_WORDS],
                ),
                4 if ORIGINAL_KEY_WORDS > 6 => last_word_anfs.sbox_bytes(),
                _ => (),
            }
            last_word_anfs ^= &rounds[old_round].columns[old_expanded_word];
            rounds[new_round].columns[new_expanded_word] = last_word_anfs;
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
