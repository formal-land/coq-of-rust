mod setup;

use {
    crate::setup::TOKEN_PROGRAM_ID,
    solana_program_test::{tokio, ProgramTest},
    solana_sdk::{
        instruction::{AccountMeta, Instruction},
        program_error::ProgramError,
        program_pack::Pack,
        pubkey::Pubkey,
        signature::{Keypair, Signer},
        system_instruction,
        transaction::Transaction,
    },
};

fn batch_instruction(instructions: Vec<Instruction>) -> Result<Instruction, ProgramError> {
    // Create a `Vec` of ordered `AccountMeta`s
    let mut accounts: Vec<AccountMeta> = vec![];
    // Start with the batch discriminator
    let mut data: Vec<u8> = vec![0xff];

    for instruction in instructions {
        // Error out on non-token IX.
        if instruction.program_id.ne(&spl_token::ID) {
            return Err(ProgramError::IncorrectProgramId);
        }

        data.push(instruction.accounts.len() as u8);
        data.push(instruction.data.len() as u8);

        data.extend_from_slice(&instruction.data);
        accounts.extend_from_slice(&instruction.accounts);
    }

    Ok(Instruction {
        program_id: spl_token::ID,
        data,
        accounts,
    })
}

#[tokio::test]
async fn batch() {
    let context = ProgramTest::new("pinocchio_token_program", TOKEN_PROGRAM_ID, None)
        .start_with_context()
        .await;

    let rent = context.banks_client.get_rent().await.unwrap();

    let mint_len = spl_token::state::Mint::LEN;
    let mint_rent = rent.minimum_balance(mint_len);

    let account_len = spl_token::state::Account::LEN;
    let account_rent = rent.minimum_balance(account_len);

    // Create a mint
    let mint_a = Keypair::new();
    let mint_authority = Keypair::new();
    let create_mint_a = system_instruction::create_account(
        &context.payer.pubkey(),
        &mint_a.pubkey(),
        mint_rent,
        mint_len as u64,
        &TOKEN_PROGRAM_ID,
    );
    let initialize_mint_ix = spl_token::instruction::initialize_mint(
        &TOKEN_PROGRAM_ID,
        &mint_a.pubkey(),
        &mint_authority.pubkey(),
        None,
        6,
    )
    .unwrap();

    // Create a mint 2 with a freeze authority
    let mint_b = Keypair::new();
    let freeze_authority = Pubkey::new_unique();
    let create_mint_b = system_instruction::create_account(
        &context.payer.pubkey(),
        &mint_b.pubkey(),
        mint_rent,
        mint_len as u64,
        &TOKEN_PROGRAM_ID,
    );
    let initialize_mint_with_freeze_authority_ix = spl_token::instruction::initialize_mint2(
        &TOKEN_PROGRAM_ID,
        &mint_b.pubkey(),
        &mint_authority.pubkey(),
        Some(&freeze_authority),
        6,
    )
    .unwrap();

    // Create 2 token accounts for mint A and 1 for mint B
    let owner_a = Keypair::new();
    let owner_b = Keypair::new();
    let owner_a_ta_a = Keypair::new();
    let owner_b_ta_a = Keypair::new();

    let create_owner_a_ta_a = system_instruction::create_account(
        &context.payer.pubkey(),
        &owner_a_ta_a.pubkey(),
        account_rent,
        account_len as u64,
        &TOKEN_PROGRAM_ID,
    );
    let create_owner_b_ta_a = system_instruction::create_account(
        &context.payer.pubkey(),
        &owner_b_ta_a.pubkey(),
        account_rent,
        account_len as u64,
        &TOKEN_PROGRAM_ID,
    );
    let intialize_owner_a_ta_a = spl_token::instruction::initialize_account3(
        &TOKEN_PROGRAM_ID,
        &owner_a_ta_a.pubkey(),
        &mint_a.pubkey(),
        &owner_a.pubkey(),
    )
    .unwrap();
    let intialize_owner_b_ta_a = spl_token::instruction::initialize_account3(
        &TOKEN_PROGRAM_ID,
        &owner_b_ta_a.pubkey(),
        &mint_a.pubkey(),
        &owner_b.pubkey(),
    )
    .unwrap();

    // Mint Token A to Owner A
    let mint_token_a_to_owner_a = spl_token::instruction::mint_to(
        &TOKEN_PROGRAM_ID,
        &mint_a.pubkey(),
        &owner_a_ta_a.pubkey(),
        &mint_authority.pubkey(),
        &[],
        1_000_000,
    )
    .unwrap();

    // Transfer Token A from Owner A to Owner B
    let transfer_token_a_to_owner_b = spl_token::instruction::transfer(
        &TOKEN_PROGRAM_ID,
        &owner_a_ta_a.pubkey(),
        &owner_b_ta_a.pubkey(),
        &owner_a.pubkey(),
        &[],
        1_000_000,
    )
    .unwrap();

    // Close Token A
    let close_owner_a_ta_a = spl_token::instruction::close_account(
        &TOKEN_PROGRAM_ID,
        &owner_a_ta_a.pubkey(),
        &owner_a.pubkey(),
        &owner_a.pubkey(),
        &[],
    )
    .unwrap();

    let batch_ix = batch_instruction(vec![
        initialize_mint_ix,
        initialize_mint_with_freeze_authority_ix,
        intialize_owner_a_ta_a,
        intialize_owner_b_ta_a,
        mint_token_a_to_owner_a,
        transfer_token_a_to_owner_b,
        close_owner_a_ta_a,
    ])
    .unwrap();

    let tx = Transaction::new_signed_with_payer(
        &[
            create_mint_a,
            create_mint_b,
            create_owner_a_ta_a,
            create_owner_b_ta_a,
            batch_ix,
        ],
        Some(&context.payer.pubkey()),
        &vec![
            &context.payer,
            &mint_a,
            &mint_b,
            &owner_a_ta_a,
            &owner_b_ta_a,
            &mint_authority,
            &owner_a,
        ],
        context.last_blockhash,
    );
    context.banks_client.process_transaction(tx).await.unwrap();

    let mint_a_account = context
        .banks_client
        .get_account(mint_a.pubkey())
        .await
        .unwrap();
    assert!(mint_a_account.is_some());
    let mint_a_account = spl_token::state::Mint::unpack(&mint_a_account.unwrap().data).unwrap();
    assert_eq!(mint_a_account.supply, 1000000);

    let mint_b_account = context
        .banks_client
        .get_account(mint_b.pubkey())
        .await
        .unwrap();
    assert!(mint_b_account.is_some());
    let mint_b_account = spl_token::state::Mint::unpack(&mint_b_account.unwrap().data).unwrap();
    assert_eq!(mint_b_account.supply, 0);

    let owner_b_ta_a_account = context
        .banks_client
        .get_account(owner_b_ta_a.pubkey())
        .await
        .unwrap();
    assert!(owner_b_ta_a_account.is_some());
    let owner_b_ta_a_account =
        spl_token::state::Account::unpack(&owner_b_ta_a_account.unwrap().data).unwrap();
    assert_eq!(owner_b_ta_a_account.amount, 1000000);
}
