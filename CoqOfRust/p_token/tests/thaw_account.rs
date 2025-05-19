mod setup;

use {
    setup::{account, mint, TOKEN_PROGRAM_ID},
    solana_program_test::{tokio, ProgramTest},
    solana_sdk::{
        program_pack::Pack,
        signature::{Keypair, Signer},
        transaction::Transaction,
    },
    spl_token::state::AccountState,
};

#[tokio::test]
async fn thaw_account() {
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

    // And a frozen token account.

    let owner = Keypair::new();

    let account =
        account::initialize(&mut context, &mint, &owner.pubkey(), &TOKEN_PROGRAM_ID).await;

    let token_account = context.banks_client.get_account(account).await.unwrap();
    assert!(token_account.is_some());

    account::freeze(
        &mut context,
        &account,
        &mint,
        &freeze_authority,
        &TOKEN_PROGRAM_ID,
    )
    .await;

    // When we thaw the account.

    let thaw_account_ix = spl_token::instruction::thaw_account(
        &spl_token::ID,
        &account,
        &mint,
        &freeze_authority.pubkey(),
        &[],
    )
    .unwrap();

    let tx = Transaction::new_signed_with_payer(
        &[thaw_account_ix],
        Some(&context.payer.pubkey()),
        &[&context.payer, &freeze_authority],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await.unwrap();

    // Then the account is frozen.

    let token_account = context.banks_client.get_account(account).await.unwrap();
    assert!(token_account.is_some());

    let token_account = token_account.unwrap();
    let token_account = spl_token::state::Account::unpack(&token_account.data).unwrap();

    assert_eq!(token_account.state, AccountState::Initialized);
}
