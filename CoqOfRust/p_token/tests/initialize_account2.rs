mod setup;

use {
    setup::{mint, TOKEN_PROGRAM_ID},
    solana_program_test::{tokio, ProgramTest},
    solana_sdk::{
        program_pack::Pack,
        pubkey::Pubkey,
        signature::{Keypair, Signer},
        system_instruction,
        transaction::Transaction,
    },
};

#[tokio::test]
async fn initialize_account2() {
    let mut context = ProgramTest::new("pinocchio_token_program", TOKEN_PROGRAM_ID, None)
        .start_with_context()
        .await;

    // Given a mint account.

    let mint_authority = Pubkey::new_unique();
    let freeze_authority = Pubkey::new_unique();

    let mint = mint::initialize(
        &mut context,
        mint_authority,
        Some(freeze_authority),
        &TOKEN_PROGRAM_ID,
    )
    .await
    .unwrap();

    // Given a mint authority, freeze authority and an account keypair.

    let owner = Pubkey::new_unique();
    let account = Keypair::new();

    let account_size = 165;
    let rent = context.banks_client.get_rent().await.unwrap();

    let initialize_ix = spl_token::instruction::initialize_account2(
        &spl_token::ID,
        &account.pubkey(),
        &mint,
        &owner,
    )
    .unwrap();

    // When a new mint account is created and initialized.

    let instructions = vec![
        system_instruction::create_account(
            &context.payer.pubkey(),
            &account.pubkey(),
            rent.minimum_balance(account_size),
            account_size as u64,
            &TOKEN_PROGRAM_ID,
        ),
        initialize_ix,
    ];

    let tx = Transaction::new_signed_with_payer(
        &instructions,
        Some(&context.payer.pubkey()),
        &[&context.payer, &account],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await.unwrap();

    // Then an account has the correct data.

    let account = context
        .banks_client
        .get_account(account.pubkey())
        .await
        .unwrap();

    assert!(account.is_some());

    let account = account.unwrap();
    let account = spl_token::state::Account::unpack(&account.data).unwrap();

    assert!(!account.is_frozen());
    assert!(account.owner == owner);
    assert!(account.mint == mint);
}
