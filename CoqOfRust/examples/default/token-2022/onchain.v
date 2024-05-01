(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module onchain.
  (*
  pub fn invoke_transfer_checked<'a>(
      token_program_id: &Pubkey,
      source_info: AccountInfo<'a>,
      mint_info: AccountInfo<'a>,
      destination_info: AccountInfo<'a>,
      authority_info: AccountInfo<'a>,
      additional_accounts: &[AccountInfo<'a>],
      amount: u64,
      decimals: u8,
      seeds: &[&[&[u8]]],
  ) -> ProgramResult {
      let mut cpi_instruction = instruction::transfer_checked(
          token_program_id,
          source_info.key,
          mint_info.key,
          destination_info.key,
          authority_info.key,
          &[], // add them later, to avoid unnecessary clones
          amount,
          decimals,
      )?;
  
      let mut cpi_account_infos = vec![
          source_info.clone(),
          mint_info.clone(),
          destination_info.clone(),
          authority_info.clone(),
      ];
  
      // if it's a signer, it might be a multisig signer, throw it in!
      additional_accounts
          .iter()
          .filter(|ai| ai.is_signer)
          .for_each(|ai| {
              cpi_account_infos.push(ai.clone());
              cpi_instruction
                  .accounts
                  .push(AccountMeta::new_readonly( *ai.key, ai.is_signer));
          });
  
      // scope the borrowing to avoid a double-borrow during CPI
      {
          let mint_data = mint_info.try_borrow_data()?;
          let mint = StateWithExtensions::<Mint>::unpack(&mint_data)?;
          if let Some(program_id) = transfer_hook::get_program_id(&mint) {
              add_extra_accounts_for_execute_cpi(
                  &mut cpi_instruction,
                  &mut cpi_account_infos,
                  &program_id,
                  source_info,
                  mint_info.clone(),
                  destination_info,
                  authority_info,
                  amount,
                  additional_accounts,
              )?;
          }
      }
  
      invoke_signed(&cpi_instruction, &cpi_account_infos, seeds)
  }
  *)
  Definition invoke_transfer_checked (τ : list Ty.t) (α : list Value.t) : M :=
    match τ, α with
    | [],
        [
          token_program_id;
          source_info;
          mint_info;
          destination_info;
          authority_info;
          additional_accounts;
          amount;
          decimals;
          seeds
        ] =>
      ltac:(M.monadic
        (let token_program_id := M.alloc (| token_program_id |) in
        let source_info := M.alloc (| source_info |) in
        let mint_info := M.alloc (| mint_info |) in
        let destination_info := M.alloc (| destination_info |) in
        let authority_info := M.alloc (| authority_info |) in
        let additional_accounts := M.alloc (| additional_accounts |) in
        let amount := M.alloc (| amount |) in
        let decimals := M.alloc (| decimals |) in
        let seeds := M.alloc (| seeds |) in
        M.catch_return (|
          ltac:(M.monadic
            (M.read (|
              let cpi_instruction :=
                M.copy (|
                  M.match_operator (|
                    M.alloc (|
                      M.call_closure (|
                        M.get_trait_method (|
                          "core::ops::try_trait::Try",
                          Ty.apply
                            (Ty.path "core::result::Result")
                            [
                              Ty.path "solana_program::instruction::Instruction";
                              Ty.path "solana_program::program_error::ProgramError"
                            ],
                          [],
                          "branch",
                          []
                        |),
                        [
                          M.call_closure (|
                            M.get_function (|
                              "spl_token_2022::instruction::transfer_checked",
                              []
                            |),
                            [
                              M.read (| token_program_id |);
                              M.read (|
                                M.get_struct_record_field
                                  source_info
                                  "solana_program::account_info::AccountInfo"
                                  "key"
                              |);
                              M.read (|
                                M.get_struct_record_field
                                  mint_info
                                  "solana_program::account_info::AccountInfo"
                                  "key"
                              |);
                              M.read (|
                                M.get_struct_record_field
                                  destination_info
                                  "solana_program::account_info::AccountInfo"
                                  "key"
                              |);
                              M.read (|
                                M.get_struct_record_field
                                  authority_info
                                  "solana_program::account_info::AccountInfo"
                                  "key"
                              |);
                              (* Unsize *) M.pointer_coercion (M.alloc (| Value.Array [] |));
                              M.read (| amount |);
                              M.read (| decimals |)
                            ]
                          |)
                        ]
                      |)
                    |),
                    [
                      fun γ =>
                        ltac:(M.monadic
                          (let γ0_0 :=
                            M.get_struct_tuple_field_or_break_match (|
                              γ,
                              "core::ops::control_flow::ControlFlow::Break",
                              0
                            |) in
                          let residual := M.copy (| γ0_0 |) in
                          M.alloc (|
                            M.never_to_any (|
                              M.read (|
                                M.return_ (|
                                  M.call_closure (|
                                    M.get_trait_method (|
                                      "core::ops::try_trait::FromResidual",
                                      Ty.apply
                                        (Ty.path "core::result::Result")
                                        [
                                          Ty.tuple [];
                                          Ty.path "solana_program::program_error::ProgramError"
                                        ],
                                      [
                                        Ty.apply
                                          (Ty.path "core::result::Result")
                                          [
                                            Ty.path "core::convert::Infallible";
                                            Ty.path "solana_program::program_error::ProgramError"
                                          ]
                                      ],
                                      "from_residual",
                                      []
                                    |),
                                    [ M.read (| residual |) ]
                                  |)
                                |)
                              |)
                            |)
                          |)));
                      fun γ =>
                        ltac:(M.monadic
                          (let γ0_0 :=
                            M.get_struct_tuple_field_or_break_match (|
                              γ,
                              "core::ops::control_flow::ControlFlow::Continue",
                              0
                            |) in
                          let val := M.copy (| γ0_0 |) in
                          val))
                    ]
                  |)
                |) in
              let cpi_account_infos :=
                M.alloc (|
                  M.call_closure (|
                    M.get_associated_function (|
                      Ty.apply
                        (Ty.path "slice")
                        [ Ty.path "solana_program::account_info::AccountInfo" ],
                      "into_vec",
                      [ Ty.path "alloc::alloc::Global" ]
                    |),
                    [
                      (* Unsize *)
                      M.pointer_coercion
                        (M.read (|
                          M.call_closure (|
                            M.get_associated_function (|
                              Ty.apply
                                (Ty.path "alloc::boxed::Box")
                                [
                                  Ty.apply
                                    (Ty.path "array")
                                    [ Ty.path "solana_program::account_info::AccountInfo" ];
                                  Ty.path "alloc::alloc::Global"
                                ],
                              "new",
                              []
                            |),
                            [
                              M.alloc (|
                                Value.Array
                                  [
                                    M.call_closure (|
                                      M.get_trait_method (|
                                        "core::clone::Clone",
                                        Ty.path "solana_program::account_info::AccountInfo",
                                        [],
                                        "clone",
                                        []
                                      |),
                                      [ source_info ]
                                    |);
                                    M.call_closure (|
                                      M.get_trait_method (|
                                        "core::clone::Clone",
                                        Ty.path "solana_program::account_info::AccountInfo",
                                        [],
                                        "clone",
                                        []
                                      |),
                                      [ mint_info ]
                                    |);
                                    M.call_closure (|
                                      M.get_trait_method (|
                                        "core::clone::Clone",
                                        Ty.path "solana_program::account_info::AccountInfo",
                                        [],
                                        "clone",
                                        []
                                      |),
                                      [ destination_info ]
                                    |);
                                    M.call_closure (|
                                      M.get_trait_method (|
                                        "core::clone::Clone",
                                        Ty.path "solana_program::account_info::AccountInfo",
                                        [],
                                        "clone",
                                        []
                                      |),
                                      [ authority_info ]
                                    |)
                                  ]
                              |)
                            ]
                          |)
                        |))
                    ]
                  |)
                |) in
              let _ :=
                M.alloc (|
                  M.call_closure (|
                    M.get_trait_method (|
                      "core::iter::traits::iterator::Iterator",
                      Ty.apply
                        (Ty.path "core::iter::adapters::filter::Filter")
                        [
                          Ty.apply
                            (Ty.path "core::slice::iter::Iter")
                            [ Ty.path "solana_program::account_info::AccountInfo" ];
                          Ty.function
                            [
                              Ty.tuple
                                [
                                  Ty.apply
                                    (Ty.path "&")
                                    [
                                      Ty.apply
                                        (Ty.path "&")
                                        [ Ty.path "solana_program::account_info::AccountInfo" ]
                                    ]
                                ]
                            ]
                            (Ty.path "bool")
                        ],
                      [],
                      "for_each",
                      [
                        Ty.function
                          [
                            Ty.tuple
                              [
                                Ty.apply
                                  (Ty.path "&")
                                  [ Ty.path "solana_program::account_info::AccountInfo" ]
                              ]
                          ]
                          (Ty.tuple [])
                      ]
                    |),
                    [
                      M.call_closure (|
                        M.get_trait_method (|
                          "core::iter::traits::iterator::Iterator",
                          Ty.apply
                            (Ty.path "core::slice::iter::Iter")
                            [ Ty.path "solana_program::account_info::AccountInfo" ],
                          [],
                          "filter",
                          [
                            Ty.function
                              [
                                Ty.tuple
                                  [
                                    Ty.apply
                                      (Ty.path "&")
                                      [
                                        Ty.apply
                                          (Ty.path "&")
                                          [ Ty.path "solana_program::account_info::AccountInfo" ]
                                      ]
                                  ]
                              ]
                              (Ty.path "bool")
                          ]
                        |),
                        [
                          M.call_closure (|
                            M.get_associated_function (|
                              Ty.apply
                                (Ty.path "slice")
                                [ Ty.path "solana_program::account_info::AccountInfo" ],
                              "iter",
                              []
                            |),
                            [ M.read (| additional_accounts |) ]
                          |);
                          M.closure
                            (fun γ =>
                              ltac:(M.monadic
                                match γ with
                                | [ α0 ] =>
                                  M.match_operator (|
                                    M.alloc (| α0 |),
                                    [
                                      fun γ =>
                                        ltac:(M.monadic
                                          (let ai := M.copy (| γ |) in
                                          M.read (|
                                            M.get_struct_record_field
                                              (M.read (| M.read (| ai |) |))
                                              "solana_program::account_info::AccountInfo"
                                              "is_signer"
                                          |)))
                                    ]
                                  |)
                                | _ => M.impossible (||)
                                end))
                        ]
                      |);
                      M.closure
                        (fun γ =>
                          ltac:(M.monadic
                            match γ with
                            | [ α0 ] =>
                              M.match_operator (|
                                M.alloc (| α0 |),
                                [
                                  fun γ =>
                                    ltac:(M.monadic
                                      (let ai := M.copy (| γ |) in
                                      M.read (|
                                        let _ :=
                                          M.alloc (|
                                            M.call_closure (|
                                              M.get_associated_function (|
                                                Ty.apply
                                                  (Ty.path "alloc::vec::Vec")
                                                  [
                                                    Ty.path
                                                      "solana_program::account_info::AccountInfo";
                                                    Ty.path "alloc::alloc::Global"
                                                  ],
                                                "push",
                                                []
                                              |),
                                              [
                                                cpi_account_infos;
                                                M.call_closure (|
                                                  M.get_trait_method (|
                                                    "core::clone::Clone",
                                                    Ty.path
                                                      "solana_program::account_info::AccountInfo",
                                                    [],
                                                    "clone",
                                                    []
                                                  |),
                                                  [ M.read (| ai |) ]
                                                |)
                                              ]
                                            |)
                                          |) in
                                        let _ :=
                                          M.alloc (|
                                            M.call_closure (|
                                              M.get_associated_function (|
                                                Ty.apply
                                                  (Ty.path "alloc::vec::Vec")
                                                  [
                                                    Ty.path
                                                      "solana_program::instruction::AccountMeta";
                                                    Ty.path "alloc::alloc::Global"
                                                  ],
                                                "push",
                                                []
                                              |),
                                              [
                                                M.get_struct_record_field
                                                  cpi_instruction
                                                  "solana_program::instruction::Instruction"
                                                  "accounts";
                                                M.call_closure (|
                                                  M.get_associated_function (|
                                                    Ty.path
                                                      "solana_program::instruction::AccountMeta",
                                                    "new_readonly",
                                                    []
                                                  |),
                                                  [
                                                    M.read (|
                                                      M.read (|
                                                        M.get_struct_record_field
                                                          (M.read (| ai |))
                                                          "solana_program::account_info::AccountInfo"
                                                          "key"
                                                      |)
                                                    |);
                                                    M.read (|
                                                      M.get_struct_record_field
                                                        (M.read (| ai |))
                                                        "solana_program::account_info::AccountInfo"
                                                        "is_signer"
                                                    |)
                                                  ]
                                                |)
                                              ]
                                            |)
                                          |) in
                                        M.alloc (| Value.Tuple [] |)
                                      |)))
                                ]
                              |)
                            | _ => M.impossible (||)
                            end))
                    ]
                  |)
                |) in
              let _ :=
                let mint_data :=
                  M.copy (|
                    M.match_operator (|
                      M.alloc (|
                        M.call_closure (|
                          M.get_trait_method (|
                            "core::ops::try_trait::Try",
                            Ty.apply
                              (Ty.path "core::result::Result")
                              [
                                Ty.apply
                                  (Ty.path "core::cell::Ref")
                                  [
                                    Ty.apply
                                      (Ty.path "&mut")
                                      [ Ty.apply (Ty.path "slice") [ Ty.path "u8" ] ]
                                  ];
                                Ty.path "solana_program::program_error::ProgramError"
                              ],
                            [],
                            "branch",
                            []
                          |),
                          [
                            M.call_closure (|
                              M.get_associated_function (|
                                Ty.path "solana_program::account_info::AccountInfo",
                                "try_borrow_data",
                                []
                              |),
                              [ mint_info ]
                            |)
                          ]
                        |)
                      |),
                      [
                        fun γ =>
                          ltac:(M.monadic
                            (let γ0_0 :=
                              M.get_struct_tuple_field_or_break_match (|
                                γ,
                                "core::ops::control_flow::ControlFlow::Break",
                                0
                              |) in
                            let residual := M.copy (| γ0_0 |) in
                            M.alloc (|
                              M.never_to_any (|
                                M.read (|
                                  M.return_ (|
                                    M.call_closure (|
                                      M.get_trait_method (|
                                        "core::ops::try_trait::FromResidual",
                                        Ty.apply
                                          (Ty.path "core::result::Result")
                                          [
                                            Ty.tuple [];
                                            Ty.path "solana_program::program_error::ProgramError"
                                          ],
                                        [
                                          Ty.apply
                                            (Ty.path "core::result::Result")
                                            [
                                              Ty.path "core::convert::Infallible";
                                              Ty.path "solana_program::program_error::ProgramError"
                                            ]
                                        ],
                                        "from_residual",
                                        []
                                      |),
                                      [ M.read (| residual |) ]
                                    |)
                                  |)
                                |)
                              |)
                            |)));
                        fun γ =>
                          ltac:(M.monadic
                            (let γ0_0 :=
                              M.get_struct_tuple_field_or_break_match (|
                                γ,
                                "core::ops::control_flow::ControlFlow::Continue",
                                0
                              |) in
                            let val := M.copy (| γ0_0 |) in
                            val))
                      ]
                    |)
                  |) in
                let mint :=
                  M.copy (|
                    M.match_operator (|
                      M.alloc (|
                        M.call_closure (|
                          M.get_trait_method (|
                            "core::ops::try_trait::Try",
                            Ty.apply
                              (Ty.path "core::result::Result")
                              [
                                Ty.apply
                                  (Ty.path "spl_token_2022::extension::StateWithExtensions")
                                  [ Ty.path "spl_token_2022::state::Mint" ];
                                Ty.path "solana_program::program_error::ProgramError"
                              ],
                            [],
                            "branch",
                            []
                          |),
                          [
                            M.call_closure (|
                              M.get_associated_function (|
                                Ty.apply
                                  (Ty.path "spl_token_2022::extension::StateWithExtensions")
                                  [ Ty.path "spl_token_2022::state::Mint" ],
                                "unpack",
                                []
                              |),
                              [
                                M.read (|
                                  M.call_closure (|
                                    M.get_trait_method (|
                                      "core::ops::deref::Deref",
                                      Ty.apply
                                        (Ty.path "core::cell::Ref")
                                        [
                                          Ty.apply
                                            (Ty.path "&mut")
                                            [ Ty.apply (Ty.path "slice") [ Ty.path "u8" ] ]
                                        ],
                                      [],
                                      "deref",
                                      []
                                    |),
                                    [ mint_data ]
                                  |)
                                |)
                              ]
                            |)
                          ]
                        |)
                      |),
                      [
                        fun γ =>
                          ltac:(M.monadic
                            (let γ0_0 :=
                              M.get_struct_tuple_field_or_break_match (|
                                γ,
                                "core::ops::control_flow::ControlFlow::Break",
                                0
                              |) in
                            let residual := M.copy (| γ0_0 |) in
                            M.alloc (|
                              M.never_to_any (|
                                M.read (|
                                  M.return_ (|
                                    M.call_closure (|
                                      M.get_trait_method (|
                                        "core::ops::try_trait::FromResidual",
                                        Ty.apply
                                          (Ty.path "core::result::Result")
                                          [
                                            Ty.tuple [];
                                            Ty.path "solana_program::program_error::ProgramError"
                                          ],
                                        [
                                          Ty.apply
                                            (Ty.path "core::result::Result")
                                            [
                                              Ty.path "core::convert::Infallible";
                                              Ty.path "solana_program::program_error::ProgramError"
                                            ]
                                        ],
                                        "from_residual",
                                        []
                                      |),
                                      [ M.read (| residual |) ]
                                    |)
                                  |)
                                |)
                              |)
                            |)));
                        fun γ =>
                          ltac:(M.monadic
                            (let γ0_0 :=
                              M.get_struct_tuple_field_or_break_match (|
                                γ,
                                "core::ops::control_flow::ControlFlow::Continue",
                                0
                              |) in
                            let val := M.copy (| γ0_0 |) in
                            val))
                      ]
                    |)
                  |) in
                M.match_operator (|
                  M.alloc (| Value.Tuple [] |),
                  [
                    fun γ =>
                      ltac:(M.monadic
                        (let γ :=
                          M.alloc (|
                            M.call_closure (|
                              M.get_function (|
                                "spl_token_2022::extension::transfer_hook::get_program_id",
                                [
                                  Ty.path "spl_token_2022::state::Mint";
                                  Ty.apply
                                    (Ty.path "spl_token_2022::extension::StateWithExtensions")
                                    [ Ty.path "spl_token_2022::state::Mint" ]
                                ]
                              |),
                              [ mint ]
                            |)
                          |) in
                        let γ0_0 :=
                          M.get_struct_tuple_field_or_break_match (|
                            γ,
                            "core::option::Option::Some",
                            0
                          |) in
                        let program_id := M.copy (| γ0_0 |) in
                        let _ :=
                          M.match_operator (|
                            M.alloc (|
                              M.call_closure (|
                                M.get_trait_method (|
                                  "core::ops::try_trait::Try",
                                  Ty.apply
                                    (Ty.path "core::result::Result")
                                    [
                                      Ty.tuple [];
                                      Ty.path "solana_program::program_error::ProgramError"
                                    ],
                                  [],
                                  "branch",
                                  []
                                |),
                                [
                                  M.call_closure (|
                                    M.get_function (|
                                      "spl_transfer_hook_interface::onchain::add_extra_accounts_for_execute_cpi",
                                      []
                                    |),
                                    [
                                      cpi_instruction;
                                      cpi_account_infos;
                                      program_id;
                                      M.read (| source_info |);
                                      M.call_closure (|
                                        M.get_trait_method (|
                                          "core::clone::Clone",
                                          Ty.path "solana_program::account_info::AccountInfo",
                                          [],
                                          "clone",
                                          []
                                        |),
                                        [ mint_info ]
                                      |);
                                      M.read (| destination_info |);
                                      M.read (| authority_info |);
                                      M.read (| amount |);
                                      M.read (| additional_accounts |)
                                    ]
                                  |)
                                ]
                              |)
                            |),
                            [
                              fun γ =>
                                ltac:(M.monadic
                                  (let γ0_0 :=
                                    M.get_struct_tuple_field_or_break_match (|
                                      γ,
                                      "core::ops::control_flow::ControlFlow::Break",
                                      0
                                    |) in
                                  let residual := M.copy (| γ0_0 |) in
                                  M.alloc (|
                                    M.never_to_any (|
                                      M.read (|
                                        M.return_ (|
                                          M.call_closure (|
                                            M.get_trait_method (|
                                              "core::ops::try_trait::FromResidual",
                                              Ty.apply
                                                (Ty.path "core::result::Result")
                                                [
                                                  Ty.tuple [];
                                                  Ty.path
                                                    "solana_program::program_error::ProgramError"
                                                ],
                                              [
                                                Ty.apply
                                                  (Ty.path "core::result::Result")
                                                  [
                                                    Ty.path "core::convert::Infallible";
                                                    Ty.path
                                                      "solana_program::program_error::ProgramError"
                                                  ]
                                              ],
                                              "from_residual",
                                              []
                                            |),
                                            [ M.read (| residual |) ]
                                          |)
                                        |)
                                      |)
                                    |)
                                  |)));
                              fun γ =>
                                ltac:(M.monadic
                                  (let γ0_0 :=
                                    M.get_struct_tuple_field_or_break_match (|
                                      γ,
                                      "core::ops::control_flow::ControlFlow::Continue",
                                      0
                                    |) in
                                  let val := M.copy (| γ0_0 |) in
                                  val))
                            ]
                          |) in
                        M.alloc (| Value.Tuple [] |)));
                    fun γ => ltac:(M.monadic (M.alloc (| Value.Tuple [] |)))
                  ]
                |) in
              M.alloc (|
                M.call_closure (|
                  M.get_function (| "solana_program::program::invoke_signed", [] |),
                  [
                    cpi_instruction;
                    M.call_closure (|
                      M.get_trait_method (|
                        "core::ops::deref::Deref",
                        Ty.apply
                          (Ty.path "alloc::vec::Vec")
                          [
                            Ty.path "solana_program::account_info::AccountInfo";
                            Ty.path "alloc::alloc::Global"
                          ],
                        [],
                        "deref",
                        []
                      |),
                      [ cpi_account_infos ]
                    |);
                    M.read (| seeds |)
                  ]
                |)
              |)
            |)))
        |)))
    | _, _ => M.impossible
    end.
End onchain.