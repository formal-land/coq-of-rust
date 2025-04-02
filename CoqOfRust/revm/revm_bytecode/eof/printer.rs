#![cfg(feature = "std")]

pub fn print(code: &[u8]) {
    use crate::opcode::*;
    use primitives::hex;

    // We can check validity and jump destinations in one pass.
    let mut i = 0;
    while i < code.len() {
        let op = code[i];
        let opcode = &OPCODE_INFO[op as usize];

        let Some(opcode) = opcode else {
            println!("Unknown opcode: 0x{:02X}", op);
            i += 1;
            continue;
        };

        if opcode.immediate_size() != 0 {
            // Check if the opcode immediate are within the bounds of the code
            if i + opcode.immediate_size() as usize >= code.len() {
                println!("Malformed code: immediate out of bounds");
                break;
            }
        }

        print!("{}", opcode.name());
        if opcode.immediate_size() != 0 {
            let immediate = &code[i + 1..i + 1 + opcode.immediate_size() as usize];
            print!(" : 0x{:}", hex::encode(immediate));
            if opcode.immediate_size() == 2 {
                print!(" ({})", i16::from_be_bytes(immediate.try_into().unwrap()));
            }
        }
        println!();

        let rjumpv_additional_immediates = 0;

        i += 1 + opcode.immediate_size() as usize + rjumpv_additional_immediates;
    }
}

#[cfg(test)]
mod test {
    use primitives::hex;

    #[test]
    fn sanity_test() {
        super::print(&hex!("6001e200ffff00"));
    }
}
