mod setup;

use {
    setup::{mint, TOKEN_PROGRAM_ID},
    solana_program_test::{tokio, ProgramTest},
    solana_sdk::{
        program_option::COption,
        program_pack::Pack,
        pubkey::Pubkey,
        signature::{Keypair, Signer},
        transaction::Transaction,
    },
    spl_token::instruction::AuthorityType,
};

#[tokio::test]
async fn set_authority() {
    let mut context = ProgramTest::new("pinocchio_token_program", TOKEN_PROGRAM_ID, None)
        .start_with_context()
        .await;

    // Given a mint account.

    let mint_authority = Keypair::new();
    let freeze_authority = Keypair::new();

    let mint = mint::initialize(
        &mut context,
        mint_authority.pubkey(),
        Some(freeze_authority.pubkey()),
        &TOKEN_PROGRAM_ID,
    )
    .await
    .unwrap();

    // When we set a new freeze authority.

    let new_authority = Pubkey::new_unique();

    let set_authority_ix = spl_token::instruction::set_authority(
        &spl_token::ID,
        &mint,
        Some(&new_authority),
        AuthorityType::FreezeAccount,
        &freeze_authority.pubkey(),
        &[],
    )
    .unwrap();

    let tx = Transaction::new_signed_with_payer(
        &[set_authority_ix],
        Some(&context.payer.pubkey()),
        &[&context.payer, &freeze_authority],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await.unwrap();

    // Then the account should have the delegate and delegated amount.

    let account = context.banks_client.get_account(mint).await.unwrap();

    assert!(account.is_some());

    let account = account.unwrap();
    let mint = spl_token::state::Mint::unpack(&account.data).unwrap();

    assert!(mint.freeze_authority == COption::Some(new_authority));
}
