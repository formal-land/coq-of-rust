use solana_sdk::pubkey::Pubkey;

#[allow(dead_code)]
pub mod account;
#[allow(dead_code)]
pub mod mint;

pub const TOKEN_PROGRAM_ID: Pubkey = Pubkey::new_from_array(spl_token_interface::program::ID);
