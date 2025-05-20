#![allow(clippy::arithmetic_side_effects)]

mod setup;

use {
    assert_matches::assert_matches,
    setup::{mint, TOKEN_PROGRAM_ID},
    solana_program_test::{tokio, BanksClientError, ProgramTest},
    solana_sdk::{
        instruction::InstructionError,
        program_pack::Pack,
        pubkey::Pubkey,
        signature::{Keypair, Signer},
        system_instruction,
        transaction::{Transaction, TransactionError},
    },
    spl_token_interface::state::{account::Account, mint::Mint, multisig::Multisig},
    std::mem::size_of,
};

#[tokio::test]
async fn withdraw_excess_lamports_from_mint() {
    let context = ProgramTest::new("pinocchio_token_program", TOKEN_PROGRAM_ID, None)
        .start_with_context()
        .await;

    let excess_lamports = 4_000_000_000_000;

    // Given a mint authority, freeze authority and an account keypair.

    let mint_authority = Keypair::new();
    let freeze_authority = Pubkey::new_unique();
    let account = Keypair::new();
    let account_pubkey = account.pubkey();

    let account_size = size_of::<Mint>();
    let rent = context.banks_client.get_rent().await.unwrap();

    let initialize_ix = spl_token::instruction::initialize_mint(
        &spl_token::ID,
        &account.pubkey(),
        &mint_authority.pubkey(),
        Some(&freeze_authority),
        0,
    )
    .unwrap();

    // And we initialize a mint account with excess lamports.

    let instructions = vec![
        system_instruction::create_account(
            &context.payer.pubkey(),
            &account.pubkey(),
            rent.minimum_balance(account_size) + excess_lamports,
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

    let account = context
        .banks_client
        .get_account(account.pubkey())
        .await
        .unwrap();

    assert!(account.is_some());

    let account = account.unwrap();
    assert_eq!(
        account.lamports,
        rent.minimum_balance(account_size) + excess_lamports
    );

    // When we withdraw the excess lamports.

    let destination = Pubkey::new_unique();

    let mut withdraw_ix = spl_token_2022::instruction::withdraw_excess_lamports(
        &spl_token_2022::ID,
        &account_pubkey,
        &destination,
        &mint_authority.pubkey(),
        &[],
    )
    .unwrap();
    // Switches the program id to the token program.
    withdraw_ix.program_id = TOKEN_PROGRAM_ID;

    let tx = Transaction::new_signed_with_payer(
        &[withdraw_ix],
        Some(&context.payer.pubkey()),
        &[&context.payer, &mint_authority],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await.unwrap();

    // Then the destination account has the excess lamports.

    let destination = context.banks_client.get_account(destination).await.unwrap();

    assert!(destination.is_some());

    let destination = destination.unwrap();
    assert_eq!(destination.lamports, excess_lamports);
}

#[tokio::test]
async fn withdraw_excess_lamports_from_account() {
    let mut context = ProgramTest::new("pinocchio_token_program", TOKEN_PROGRAM_ID, None)
        .start_with_context()
        .await;

    let excess_lamports = 4_000_000_000_000;

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

    let owner = Keypair::new();
    let account = Keypair::new();
    let account_pubkey = account.pubkey();

    let account_size = size_of::<Account>();
    let rent = context.banks_client.get_rent().await.unwrap();

    let initialize_ix = spl_token::instruction::initialize_account(
        &spl_token::ID,
        &account.pubkey(),
        &mint,
        &owner.pubkey(),
    )
    .unwrap();

    // When a new mint account is created and initialized.

    let instructions = vec![
        system_instruction::create_account(
            &context.payer.pubkey(),
            &account.pubkey(),
            rent.minimum_balance(account_size) + excess_lamports,
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

    let account = context
        .banks_client
        .get_account(account.pubkey())
        .await
        .unwrap();

    assert!(account.is_some());

    let account = account.unwrap();
    assert_eq!(
        account.lamports,
        rent.minimum_balance(account_size) + excess_lamports
    );

    // When we withdraw the excess lamports.

    let destination = Pubkey::new_unique();

    let mut withdraw_ix = spl_token_2022::instruction::withdraw_excess_lamports(
        &spl_token_2022::ID,
        &account_pubkey,
        &destination,
        &owner.pubkey(),
        &[],
    )
    .unwrap();
    // Switches the program id to the token program.
    withdraw_ix.program_id = TOKEN_PROGRAM_ID;

    let tx = Transaction::new_signed_with_payer(
        &[withdraw_ix],
        Some(&context.payer.pubkey()),
        &[&context.payer, &owner],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await.unwrap();

    // Then the destination account has the excess lamports.

    let destination = context.banks_client.get_account(destination).await.unwrap();

    assert!(destination.is_some());

    let destination = destination.unwrap();
    assert_eq!(destination.lamports, excess_lamports);
}

#[tokio::test]
async fn withdraw_excess_lamports_from_multisig() {
    let context = ProgramTest::new("pinocchio_token_program", TOKEN_PROGRAM_ID, None)
        .start_with_context()
        .await;

    let excess_lamports = 4_000_000_000_000;

    // Given an account

    let multisig = Keypair::new();
    let signer1 = Keypair::new();
    let signer1_pubkey = signer1.pubkey();
    let signer2 = Keypair::new();
    let signer2_pubkey = signer2.pubkey();
    let signer3 = Keypair::new();
    let signer3_pubkey = signer3.pubkey();
    let signers = vec![&signer1_pubkey, &signer2_pubkey, &signer3_pubkey];

    let rent = context.banks_client.get_rent().await.unwrap();
    let account_size = size_of::<Multisig>();

    let initialize_ix = spl_token::instruction::initialize_multisig(
        &spl_token::ID,
        &multisig.pubkey(),
        &signers,
        3,
    )
    .unwrap();

    // And we initialize the multisig account.

    let instructions = vec![
        system_instruction::create_account(
            &context.payer.pubkey(),
            &multisig.pubkey(),
            rent.minimum_balance(account_size) + excess_lamports,
            account_size as u64,
            &TOKEN_PROGRAM_ID,
        ),
        initialize_ix,
    ];

    let tx = Transaction::new_signed_with_payer(
        &instructions,
        Some(&context.payer.pubkey()),
        &[&context.payer, &multisig],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await.unwrap();

    let account = context
        .banks_client
        .get_account(multisig.pubkey())
        .await
        .unwrap();

    assert!(account.is_some());

    let account = account.unwrap();
    assert_eq!(
        account.lamports,
        rent.minimum_balance(account_size) + excess_lamports
    );

    // When we withdraw the excess lamports.

    let destination = Pubkey::new_unique();

    let mut withdraw_ix = spl_token_2022::instruction::withdraw_excess_lamports(
        &spl_token_2022::ID,
        &multisig.pubkey(),
        &destination,
        &multisig.pubkey(),
        &signers,
    )
    .unwrap();
    // Switches the program id to the token program.
    withdraw_ix.program_id = TOKEN_PROGRAM_ID;

    let tx = Transaction::new_signed_with_payer(
        &[withdraw_ix],
        Some(&context.payer.pubkey()),
        &[&context.payer, &signer1, &signer2, &signer3],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await.unwrap();

    // Then the destination account has the excess lamports.

    let destination = context.banks_client.get_account(destination).await.unwrap();

    assert!(destination.is_some());

    let destination = destination.unwrap();
    assert_eq!(destination.lamports, excess_lamports);
}

#[tokio::test]
async fn fail_withdraw_excess_lamports_from_mint_wrong_authority() {
    let context = ProgramTest::new("pinocchio_token_program", TOKEN_PROGRAM_ID, None)
        .start_with_context()
        .await;

    let excess_lamports = 4_000_000_000_000;

    // Given a mint authority, freeze authority and an account keypair.

    let mint_authority = Keypair::new();
    let freeze_authority = Pubkey::new_unique();
    let account = Keypair::new();
    let account_pubkey = account.pubkey();

    let account_size = size_of::<Mint>();
    let rent = context.banks_client.get_rent().await.unwrap();

    let initialize_ix = spl_token::instruction::initialize_mint(
        &spl_token::ID,
        &account.pubkey(),
        &mint_authority.pubkey(),
        Some(&freeze_authority),
        0,
    )
    .unwrap();

    // And we initialize a mint account with excess lamports.

    let instructions = vec![
        system_instruction::create_account(
            &context.payer.pubkey(),
            &account.pubkey(),
            rent.minimum_balance(account_size) + excess_lamports,
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

    let account = context
        .banks_client
        .get_account(account.pubkey())
        .await
        .unwrap();

    assert!(account.is_some());

    let account = account.unwrap();
    assert_eq!(
        account.lamports,
        rent.minimum_balance(account_size) + excess_lamports
    );

    // When we try to withdraw the excess lamports with the wrong authority.

    let destination = Pubkey::new_unique();
    let wrong_authority = Keypair::new();

    let mut withdraw_ix = spl_token_2022::instruction::withdraw_excess_lamports(
        &spl_token_2022::ID,
        &account_pubkey,
        &destination,
        &wrong_authority.pubkey(),
        &[],
    )
    .unwrap();
    // Switches the program id to the token program.
    withdraw_ix.program_id = TOKEN_PROGRAM_ID;

    let tx = Transaction::new_signed_with_payer(
        &[withdraw_ix],
        Some(&context.payer.pubkey()),
        &[&context.payer, &wrong_authority],
        context.last_blockhash,
    );
    let error = context
        .banks_client
        .process_transaction(tx)
        .await
        .unwrap_err();

    // The we expect an error.

    assert_matches!(
        error,
        BanksClientError::TransactionError(TransactionError::InstructionError(
            _,
            InstructionError::Custom(4) // TokenError::OwnerMismatch
        ))
    );
}

#[tokio::test]
async fn fail_withdraw_excess_lamports_from_account_wrong_authority() {
    let mut context = ProgramTest::new("pinocchio_token_program", TOKEN_PROGRAM_ID, None)
        .start_with_context()
        .await;

    let excess_lamports = 4_000_000_000_000;

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

    let owner = Keypair::new();
    let account = Keypair::new();
    let account_pubkey = account.pubkey();

    let account_size = size_of::<Account>();
    let rent = context.banks_client.get_rent().await.unwrap();

    let initialize_ix = spl_token::instruction::initialize_account(
        &spl_token::ID,
        &account.pubkey(),
        &mint,
        &owner.pubkey(),
    )
    .unwrap();

    // When a new mint account is created and initialized.

    let instructions = vec![
        system_instruction::create_account(
            &context.payer.pubkey(),
            &account.pubkey(),
            rent.minimum_balance(account_size) + excess_lamports,
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

    let account = context
        .banks_client
        .get_account(account.pubkey())
        .await
        .unwrap();

    assert!(account.is_some());

    let account = account.unwrap();
    assert_eq!(
        account.lamports,
        rent.minimum_balance(account_size) + excess_lamports
    );

    // When we try to withdraw the excess lamports with the wrong owner.

    let destination = Pubkey::new_unique();
    let wrong_owner = Keypair::new();

    let mut withdraw_ix = spl_token_2022::instruction::withdraw_excess_lamports(
        &spl_token_2022::ID,
        &account_pubkey,
        &destination,
        &wrong_owner.pubkey(),
        &[],
    )
    .unwrap();
    // Switches the program id to the token program.
    withdraw_ix.program_id = TOKEN_PROGRAM_ID;

    let tx = Transaction::new_signed_with_payer(
        &[withdraw_ix],
        Some(&context.payer.pubkey()),
        &[&context.payer, &wrong_owner],
        context.last_blockhash,
    );
    let error = context
        .banks_client
        .process_transaction(tx)
        .await
        .unwrap_err();

    // The we expect an error.

    assert_matches!(
        error,
        BanksClientError::TransactionError(TransactionError::InstructionError(
            _,
            InstructionError::Custom(4) // TokenError::OwnerMismatch
        ))
    );
}

#[tokio::test]
async fn fail_withdraw_excess_lamports_from_multisig_wrong_authority() {
    let context = ProgramTest::new("pinocchio_token_program", TOKEN_PROGRAM_ID, None)
        .start_with_context()
        .await;

    let excess_lamports = 4_000_000_000_000;

    // Given an account

    let multisig = Keypair::new();
    let signer1 = Keypair::new();
    let signer1_pubkey = signer1.pubkey();
    let signer2 = Keypair::new();
    let signer2_pubkey = signer2.pubkey();
    let signer3 = Keypair::new();
    let signer3_pubkey = signer3.pubkey();
    let signers = vec![&signer1_pubkey, &signer2_pubkey, &signer3_pubkey];

    let rent = context.banks_client.get_rent().await.unwrap();
    let account_size = size_of::<Multisig>();

    let initialize_ix = spl_token::instruction::initialize_multisig(
        &spl_token::ID,
        &multisig.pubkey(),
        &signers,
        3,
    )
    .unwrap();

    // And we initialize the multisig account.

    let instructions = vec![
        system_instruction::create_account(
            &context.payer.pubkey(),
            &multisig.pubkey(),
            rent.minimum_balance(account_size) + excess_lamports,
            account_size as u64,
            &TOKEN_PROGRAM_ID,
        ),
        initialize_ix,
    ];

    let tx = Transaction::new_signed_with_payer(
        &instructions,
        Some(&context.payer.pubkey()),
        &[&context.payer, &multisig],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await.unwrap();

    let account = context
        .banks_client
        .get_account(multisig.pubkey())
        .await
        .unwrap();

    assert!(account.is_some());

    let account = account.unwrap();
    assert_eq!(
        account.lamports,
        rent.minimum_balance(account_size) + excess_lamports
    );

    // When we try to withdraw the excess lamports with the wrong authority.

    let destination = Pubkey::new_unique();
    let wrong_authority = Keypair::new();

    let mut withdraw_ix = spl_token_2022::instruction::withdraw_excess_lamports(
        &spl_token_2022::ID,
        &multisig.pubkey(),
        &destination,
        &wrong_authority.pubkey(),
        &signers,
    )
    .unwrap();
    // Switches the program id to the token program.
    withdraw_ix.program_id = TOKEN_PROGRAM_ID;

    let tx = Transaction::new_signed_with_payer(
        &[withdraw_ix],
        Some(&context.payer.pubkey()),
        &[&context.payer, &signer1, &signer2, &signer3],
        context.last_blockhash,
    );
    let error = context
        .banks_client
        .process_transaction(tx)
        .await
        .unwrap_err();

    // The we expect an error.

    assert_matches!(
        error,
        BanksClientError::TransactionError(TransactionError::InstructionError(
            _,
            InstructionError::Custom(4) // TokenError::OwnerMismatch
        ))
    );
}

#[tokio::test]
async fn fail_withdraw_excess_lamports_from_multisig_missing_signer() {
    let context = ProgramTest::new("pinocchio_token_program", TOKEN_PROGRAM_ID, None)
        .start_with_context()
        .await;

    let excess_lamports = 4_000_000_000_000;

    // Given an account

    let multisig = Keypair::new();
    let signer1 = Keypair::new();
    let signer1_pubkey = signer1.pubkey();
    let signer2 = Keypair::new();
    let signer2_pubkey = signer2.pubkey();
    let signer3 = Keypair::new();
    let signer3_pubkey = signer3.pubkey();
    let signers = vec![&signer1_pubkey, &signer2_pubkey, &signer3_pubkey];

    let rent = context.banks_client.get_rent().await.unwrap();
    let account_size = size_of::<Multisig>();

    let initialize_ix = spl_token::instruction::initialize_multisig(
        &spl_token::ID,
        &multisig.pubkey(),
        &signers,
        3,
    )
    .unwrap();

    // And we initialize the multisig account.

    let instructions = vec![
        system_instruction::create_account(
            &context.payer.pubkey(),
            &multisig.pubkey(),
            rent.minimum_balance(account_size) + excess_lamports,
            account_size as u64,
            &TOKEN_PROGRAM_ID,
        ),
        initialize_ix,
    ];

    let tx = Transaction::new_signed_with_payer(
        &instructions,
        Some(&context.payer.pubkey()),
        &[&context.payer, &multisig],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await.unwrap();

    let account = context
        .banks_client
        .get_account(multisig.pubkey())
        .await
        .unwrap();

    assert!(account.is_some());

    let account = account.unwrap();
    assert_eq!(
        account.lamports,
        rent.minimum_balance(account_size) + excess_lamports
    );

    // When we try to withdraw the excess lamports with the wrong authority.

    let destination = Pubkey::new_unique();

    let mut withdraw_ix = spl_token_2022::instruction::withdraw_excess_lamports(
        &spl_token_2022::ID,
        &multisig.pubkey(),
        &destination,
        &multisig.pubkey(),
        &[&signer1_pubkey, &signer2_pubkey],
    )
    .unwrap();
    // Switches the program id to the token program.
    withdraw_ix.program_id = TOKEN_PROGRAM_ID;

    let tx = Transaction::new_signed_with_payer(
        &[withdraw_ix],
        Some(&context.payer.pubkey()),
        &[&context.payer, &signer1, &signer2],
        context.last_blockhash,
    );
    let error = context
        .banks_client
        .process_transaction(tx)
        .await
        .unwrap_err();

    // The we expect an error.

    assert_matches!(
        error,
        BanksClientError::TransactionError(TransactionError::InstructionError(
            _,
            InstructionError::MissingRequiredSignature
        ))
    );
}

#[tokio::test]
async fn withdraw_excess_lamports_from_mint_with_no_authority() {
    let context = ProgramTest::new("pinocchio_token_program", TOKEN_PROGRAM_ID, None)
        .start_with_context()
        .await;

    let excess_lamports = 4_000_000_000_000;

    // Given a mint authority, freeze authority and an account keypair.

    let mint_authority = Keypair::new();
    let freeze_authority = Pubkey::new_unique();
    let mint_account = Keypair::new();
    let account_pubkey = mint_account.pubkey();

    let account_size = size_of::<Mint>();
    let rent = context.banks_client.get_rent().await.unwrap();

    let initialize_ix = spl_token::instruction::initialize_mint(
        &spl_token::ID,
        &mint_account.pubkey(),
        &mint_authority.pubkey(),
        Some(&freeze_authority),
        0,
    )
    .unwrap();

    // And we initialize a mint account with excess lamports.

    let instructions = vec![
        system_instruction::create_account(
            &context.payer.pubkey(),
            &mint_account.pubkey(),
            rent.minimum_balance(account_size) + excess_lamports,
            account_size as u64,
            &TOKEN_PROGRAM_ID,
        ),
        initialize_ix,
    ];

    let tx = Transaction::new_signed_with_payer(
        &instructions,
        Some(&context.payer.pubkey()),
        &[&context.payer, &mint_account],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await.unwrap();

    let account = context
        .banks_client
        .get_account(mint_account.pubkey())
        .await
        .unwrap();

    assert!(account.is_some());

    let account = account.unwrap();
    assert_eq!(
        account.lamports,
        rent.minimum_balance(account_size) + excess_lamports
    );

    // And we remove the mint authority.

    let set_authority_ix = spl_token::instruction::set_authority(
        &spl_token::ID,
        &mint_account.pubkey(),
        None,
        spl_token::instruction::AuthorityType::MintTokens,
        &mint_authority.pubkey(),
        &[&mint_authority.pubkey()],
    )
    .unwrap();

    let tx = Transaction::new_signed_with_payer(
        &[set_authority_ix],
        Some(&context.payer.pubkey()),
        &[&context.payer, &mint_authority],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await.unwrap();

    let account = context
        .banks_client
        .get_account(mint_account.pubkey())
        .await
        .unwrap();

    assert!(account.is_some());

    let account = account.unwrap();
    let account = spl_token::state::Mint::unpack(&account.data).unwrap();

    assert!(account.mint_authority.is_none());

    // When we withdraw the excess lamports with no authority.

    let destination = Pubkey::new_unique();

    let mut withdraw_ix = spl_token_2022::instruction::withdraw_excess_lamports(
        &spl_token_2022::ID,
        &account_pubkey,
        &destination,
        &mint_account.pubkey(),
        &[],
    )
    .unwrap();
    // Switches the program id to the token program.
    withdraw_ix.program_id = TOKEN_PROGRAM_ID;

    let tx = Transaction::new_signed_with_payer(
        &[withdraw_ix],
        Some(&context.payer.pubkey()),
        &[&context.payer, &mint_account],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await.unwrap();

    // Then the destination account has the excess lamports.

    let destination = context.banks_client.get_account(destination).await.unwrap();

    assert!(destination.is_some());

    let destination = destination.unwrap();
    assert_eq!(destination.lamports, excess_lamports);
}

#[tokio::test]
async fn fail_withdraw_excess_lamports_from_mint_with_authority_and_mint_as_signer() {
    let context = ProgramTest::new("pinocchio_token_program", TOKEN_PROGRAM_ID, None)
        .start_with_context()
        .await;

    let excess_lamports = 4_000_000_000_000;

    // Given a mint authority, freeze authority and an account keypair.

    let mint_authority = Keypair::new();
    let freeze_authority = Pubkey::new_unique();
    let mint_account = Keypair::new();
    let account_pubkey = mint_account.pubkey();

    let account_size = size_of::<Mint>();
    let rent = context.banks_client.get_rent().await.unwrap();

    let initialize_ix = spl_token::instruction::initialize_mint(
        &spl_token::ID,
        &mint_account.pubkey(),
        &mint_authority.pubkey(),
        Some(&freeze_authority),
        0,
    )
    .unwrap();

    // And we initialize a mint account with excess lamports.

    let instructions = vec![
        system_instruction::create_account(
            &context.payer.pubkey(),
            &mint_account.pubkey(),
            rent.minimum_balance(account_size) + excess_lamports,
            account_size as u64,
            &TOKEN_PROGRAM_ID,
        ),
        initialize_ix,
    ];

    let tx = Transaction::new_signed_with_payer(
        &instructions,
        Some(&context.payer.pubkey()),
        &[&context.payer, &mint_account],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await.unwrap();

    let account = context
        .banks_client
        .get_account(mint_account.pubkey())
        .await
        .unwrap();

    assert!(account.is_some());

    let account = account.unwrap();
    assert_eq!(
        account.lamports,
        rent.minimum_balance(account_size) + excess_lamports
    );

    // When we try to withdraw the excess lamports with the mint as authority.

    let destination = Pubkey::new_unique();

    let mut withdraw_ix = spl_token_2022::instruction::withdraw_excess_lamports(
        &spl_token_2022::ID,
        &account_pubkey,
        &destination,
        &mint_account.pubkey(),
        &[],
    )
    .unwrap();
    // Switches the program id to the token program.
    withdraw_ix.program_id = TOKEN_PROGRAM_ID;

    let tx = Transaction::new_signed_with_payer(
        &[withdraw_ix],
        Some(&context.payer.pubkey()),
        &[&context.payer, &mint_account],
        context.last_blockhash,
    );
    let error = context
        .banks_client
        .process_transaction(tx)
        .await
        .unwrap_err();

    // Then we expect an error.

    assert_matches!(
        error,
        BanksClientError::TransactionError(TransactionError::InstructionError(
            _,
            InstructionError::Custom(4) // TokenError::OwnerMismatch
        ))
    );
}

#[tokio::test]
async fn fail_withdraw_excess_lamports_from_mint_with_no_authority_and_authority_signer() {
    let context = ProgramTest::new("pinocchio_token_program", TOKEN_PROGRAM_ID, None)
        .start_with_context()
        .await;

    let excess_lamports = 4_000_000_000_000;

    // Given a mint authority, freeze authority and an account keypair.

    let mint_authority = Keypair::new();
    let freeze_authority = Pubkey::new_unique();
    let mint_account = Keypair::new();
    let account_pubkey = mint_account.pubkey();

    let account_size = size_of::<Mint>();
    let rent = context.banks_client.get_rent().await.unwrap();

    let initialize_ix = spl_token::instruction::initialize_mint(
        &spl_token::ID,
        &mint_account.pubkey(),
        &mint_authority.pubkey(),
        Some(&freeze_authority),
        0,
    )
    .unwrap();

    // And we initialize a mint account with excess lamports.

    let instructions = vec![
        system_instruction::create_account(
            &context.payer.pubkey(),
            &mint_account.pubkey(),
            rent.minimum_balance(account_size) + excess_lamports,
            account_size as u64,
            &TOKEN_PROGRAM_ID,
        ),
        initialize_ix,
    ];

    let tx = Transaction::new_signed_with_payer(
        &instructions,
        Some(&context.payer.pubkey()),
        &[&context.payer, &mint_account],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await.unwrap();

    let account = context
        .banks_client
        .get_account(mint_account.pubkey())
        .await
        .unwrap();

    assert!(account.is_some());

    let account = account.unwrap();
    assert_eq!(
        account.lamports,
        rent.minimum_balance(account_size) + excess_lamports
    );

    // And we remove the mint authority.

    let set_authority_ix = spl_token::instruction::set_authority(
        &spl_token::ID,
        &mint_account.pubkey(),
        None,
        spl_token::instruction::AuthorityType::MintTokens,
        &mint_authority.pubkey(),
        &[&mint_authority.pubkey()],
    )
    .unwrap();

    let tx = Transaction::new_signed_with_payer(
        &[set_authority_ix],
        Some(&context.payer.pubkey()),
        &[&context.payer, &mint_authority],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await.unwrap();

    let account = context
        .banks_client
        .get_account(mint_account.pubkey())
        .await
        .unwrap();

    assert!(account.is_some());

    let account = account.unwrap();
    let account = spl_token::state::Mint::unpack(&account.data).unwrap();

    assert!(account.mint_authority.is_none());

    // When we try to withdraw the excess lamports with the "old" mint authority.

    let destination = Pubkey::new_unique();

    let mut withdraw_ix = spl_token_2022::instruction::withdraw_excess_lamports(
        &spl_token_2022::ID,
        &account_pubkey,
        &destination,
        &mint_authority.pubkey(),
        &[],
    )
    .unwrap();
    // Switches the program id to the token program.
    withdraw_ix.program_id = TOKEN_PROGRAM_ID;

    let tx = Transaction::new_signed_with_payer(
        &[withdraw_ix],
        Some(&context.payer.pubkey()),
        &[&context.payer, &mint_authority],
        context.last_blockhash,
    );
    let error = context
        .banks_client
        .process_transaction(tx)
        .await
        .unwrap_err();

    // Then we expect an error.

    assert_matches!(
        error,
        BanksClientError::TransactionError(TransactionError::InstructionError(
            _,
            InstructionError::Custom(15) // TokenError::AuthorityTypeNotSupported
        ))
    );
}
