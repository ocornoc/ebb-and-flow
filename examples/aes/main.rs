mod block;
mod key_schedule;
mod linear;

/*
fn mix_byte_0(col: u32) -> u8 {
    let [byte0, byte1, byte2, byte3] = (col as u32).to_le_bytes();
    ByteANFs::gmul(sbox(byte0), 2)
    ^ ByteANFs::gmul(sbox(byte1), 3)
    ^ byte2
    ^ byte3
}
*/

/* 
fn sboxes() {
    let sbox_anfs = U8ANFs::sbox();
    for (i, anf) in sbox_anfs.anf.iter().enumerate() {
        println!("sbox bit {i}: {anf}")
    }
    let inv_sbox_anfs = U8ANFs::inverse_sbox();
    for (i, anf) in inv_sbox_anfs.anf.iter().enumerate() {
        println!("inv sbox bit {i}: {anf}")
    }
}

fn sboxes_times() {
    for multiple in [1_u8, 2, 3/*, 9, 11, 13, 14*/] {
        let sbox_times = U8ANFs::sbox_times(multiple);
        for (bit, anf) in sbox_times.anf.iter().enumerate() {
            println!("sbox * {multiple} bit {bit}: {anf}")
        }
    }
}

fn ids() {
    let id = U8ANFs::id();
    for (bit, anf) in id.anf.iter().enumerate() {
            println!("id bit {bit}: {anf}")
    }
}
*/

/*
fn mix_threads() {
    let mut handles = Vec::with_capacity(8);
    for bit in 0..8 {
        handles.push(std::thread::spawn(move || linear::XorAnds::from_assignments(32, |assignment| {
            mix_byte_0(assignment as u32) & (1 << bit) != 0
        })));
    }
    for (i, handle) in handles.into_iter().enumerate() {
        let anf = handle.join().unwrap();
        let mut stdout = std::io::stdout().lock();
        writeln!(stdout, "mixcols bit {i}: {anf}").unwrap();
    }
}
*/

fn main() {
    /*
    ids();
    sboxes();
    for multiple in [2, 3, 9, 11, 13, 14] {
        print!("x * {multiple}:\n{}", U8ANFs::x_times(multiple));
    }
    sboxes_times();
    let key_schedule = block::KeySchedule::from_any_key();
    let last_round = key_schedule.rounds.last().unwrap();
    let last_expanded_word = last_round.expanded.last().unwrap();
    let last_byte = last_expanded_word.bytes.last().unwrap();
    print!("last byte of key schedule:\n{last_byte}");
    let mut block = block::Block::id();
    block.encrypt(&key_schedule);
    print!("last byte of block:\n{}", block.columns[3].bytes[3]);
    //mix_threads();
    */
}
