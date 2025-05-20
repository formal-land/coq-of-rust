use {
    solana_program_test::{BanksClientError, ProgramTestContext},
    solana_sdk::{
        program_error::ProgramError, pubkey::Pubkey, signature::Keypair, signer::Signer,
        system_instruction, transaction::Transaction,
    },
    spl_token_interface::state::mint::Mint,
    std::mem::size_of,
};

pub async fn initialize(
    context: &mut ProgramTestContext,
    mint_authority: Pubkey,
    freeze_authority: Option<Pubkey>,
    program_id: &Pubkey,
) -> Result<Pubkey, ProgramError> {
    // Mint account keypair.
    let account = Keypair::new();

    let account_size = size_of::<Mint>();
    let rent = context.banks_client.get_rent().await.unwrap();

    let mut initialize_ix = spl_token::instruction::initialize_mint(
        &spl_token::ID,
        &account.pubkey(),
        &mint_authority,
        freeze_authority.as_ref(),
        4,
    )
    .unwrap();
    // Switches the program id in case we are using a "custom" one.
    initialize_ix.program_id = *program_id;

    // Create a new account and initialize as a mint.

    let instructions = vec![
        system_instruction::create_account(
            &context.payer.pubkey(),
            &account.pubkey(),
            rent.minimum_balance(account_size),
            account_size as u64,
            program_id,
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

    Ok(account.pubkey())
}

pub async fn mint(
    context: &mut ProgramTestContext,
    mint: &Pubkey,
    account: &Pubkey,
    mint_authority: &Keypair,
    amount: u64,
    program_id: &Pubkey,
) -> Result<(), BanksClientError> {
    let mut mint_ix = spl_token::instruction::mint_to(
        &spl_token::ID,
        mint,
        account,
        &mint_authority.pubkey(),
        &[],
        amount,
    )
    .unwrap();
    // Switches the program id to the token program.
    mint_ix.program_id = *program_id;

    let tx = Transaction::new_signed_with_payer(
        &[mint_ix],
        Some(&context.payer.pubkey()),
        &[&context.payer, mint_authority],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await
}
