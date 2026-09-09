Require Import RocqOfRust.RocqOfRust.
Require Import core.convert.num.
Require Import core.num.mod.
Require Import evaluate.translated.
Require Import evaluate.ocaml.
Require Import ruint.algorithms.mod.
Require Import ruint.algorithms.ops.
Require Import ruint.lib.
Require Import ruint.utils.

Definition uint_128_2 : Ty.t :=
  Ty.apply
    (Ty.path "ruint::Uint")
    [
      Value.Integer IntegerKind.Usize 128;
      Value.Integer IntegerKind.Usize 2
    ]
    [].

Definition intrinsic_wrapping_sub : PolymorphicFunction.t :=
  fun generic_consts generic_tys args =>
    match generic_consts, generic_tys, args with
    | [], [ ty ], [ lhs; rhs ] =>
      M.call_closure ty BinOp.Wrap.sub [ lhs; rhs ]
    | _, _, _ => M.impossible "wrong arguments for wrapping_sub"
    end.

Definition slice_u64 : Ty.t :=
  Ty.apply (Ty.path "slice") [] [ Ty.path "u64" ].

Definition range_usize : Ty.t :=
  Ty.apply (Ty.path "core::ops::range::Range") [] [ Ty.path "usize" ].

Definition slice_len : PolymorphicFunction.t :=
  fun generic_consts generic_tys args =>
    match generic_consts, generic_tys, args with
    | [], [], [ self ] =>
      M.let_
        (M.read self)
        (fun value =>
          match value with
          | Value.Array values =>
            M.pure
              (Value.Integer IntegerKind.Usize (Z.of_nat (List.length values)))
          | _ => M.impossible "slice len expected an array"
          end)
    | _, _, _ => M.impossible "wrong arguments for slice len"
    end.

Definition range_into_iter : PolymorphicFunction.t :=
  fun generic_consts generic_tys args =>
    match generic_consts, generic_tys, args with
    | [], [], [ range ] => M.pure range
    | _, _, _ => M.impossible "wrong arguments for Range into_iter"
    end.

Definition range_next : PolymorphicFunction.t :=
  fun generic_consts generic_tys args =>
    match generic_consts, generic_tys, args with
    | [], [], [ range ] =>
      M.let_
        (M.read range)
        (fun value =>
          match value with
          | Value.StructRecord constructor consts tys fields =>
            match List.assoc fields "start", List.assoc fields "end_" with
            | Some (Value.Integer IntegerKind.Usize start),
                Some (Value.Integer IntegerKind.Usize end_) =>
              if Z.ltb start end_ then
                M.let_
                  (M.write
                    range
                    (Value.mkStructRecord
                      constructor
                      consts
                      tys
                      [
                        ("start", Value.Integer IntegerKind.Usize (start + 1));
                        ("end_", Value.Integer IntegerKind.Usize end_)
                      ]))
                  (fun _ =>
                    M.pure
                      (Value.StructTuple
                        "core::option::Option::Some"
                        []
                        [ Ty.path "usize" ]
                        [ Value.Integer IntegerKind.Usize start ]))
              else
                M.pure
                  (Value.StructTuple
                    "core::option::Option::None"
                    []
                    [ Ty.path "usize" ]
                    [])
            | _, _ => M.impossible "Range fields are missing"
            end
          | _ => M.impossible "Range next expected a range"
          end)
    | _, _, _ => M.impossible "wrong arguments for Range next"
    end.

Fixpoint u64_values_eqb (lhs rhs : list Value.t) : bool :=
  match lhs, rhs with
  | [], [] => true
  | Value.Integer IntegerKind.U64 lhs_value :: lhs_values,
      Value.Integer IntegerKind.U64 rhs_value :: rhs_values =>
    andb
      (Z.eqb lhs_value rhs_value)
      (u64_values_eqb lhs_values rhs_values)
  | _, _ => false
  end.

Definition array_u64_eq : PolymorphicFunction.t :=
  fun generic_consts generic_tys args =>
    match generic_consts, generic_tys, args with
    | [], [], [ lhs; rhs ] =>
      M.let_
        (M.read lhs)
        (fun lhs =>
          M.let_
            (M.read rhs)
            (fun rhs =>
              match lhs, rhs with
              | Value.Array lhs, Value.Array rhs =>
                M.pure (Value.Bool (u64_values_eqb lhs rhs))
              | _, _ => M.impossible "array equality expected arrays"
              end))
    | _, _, _ => M.impossible "wrong arguments for array equality"
    end.

Definition array_u64_2 : Ty.t :=
  Ty.apply
    (Ty.path "array")
    [ Value.Integer IntegerKind.Usize 2 ]
    [ Ty.path "u64" ].

Definition runtime : Translated.Runtime.t :=
  Translated.Runtime.of_all_tables
    [
      ("core::intrinsics::wrapping_sub", intrinsic_wrapping_sub);
      ("ruint::mask", mask);
      ("ruint::nlimbs", nlimbs)
    ]
    [
      (Ty.path "u128", "wrapping_sub", num.Impl_u128.wrapping_sub);
      (Ty.path "u64", "wrapping_neg", num.Impl_u64.wrapping_neg);
      (Ty.path "u64", "wrapping_sub", num.Impl_u64.wrapping_sub);
      (slice_u64, "len", slice_len);
      (uint_128_2,
        "BITS",
        Impl_ruint_Uint_BITS_LIMBS.value_BITS
          (Value.Integer IntegerKind.Usize 128)
          (Value.Integer IntegerKind.Usize 2));
      (uint_128_2,
        "LIMBS",
        Impl_ruint_Uint_BITS_LIMBS.value_LIMBS
          (Value.Integer IntegerKind.Usize 128)
          (Value.Integer IntegerKind.Usize 2));
      (uint_128_2,
        "MASK",
        Impl_ruint_Uint_BITS_LIMBS.value_MASK
          (Value.Integer IntegerKind.Usize 128)
          (Value.Integer IntegerKind.Usize 2));
      (uint_128_2,
        "MIN",
        Impl_ruint_Uint_BITS_LIMBS.value_MIN
          (Value.Integer IntegerKind.Usize 128)
          (Value.Integer IntegerKind.Usize 2));
      (uint_128_2,
        "MAX",
        Impl_ruint_Uint_BITS_LIMBS.value_MAX
          (Value.Integer IntegerKind.Usize 128)
          (Value.Integer IntegerKind.Usize 2));
      (uint_128_2,
        "ZERO",
        Impl_ruint_Uint_BITS_LIMBS.value_ZERO
          (Value.Integer IntegerKind.Usize 128)
          (Value.Integer IntegerKind.Usize 2));
      (uint_128_2,
        "from_limbs",
        Impl_ruint_Uint_BITS_LIMBS.from_limbs
          (Value.Integer IntegerKind.Usize 128)
          (Value.Integer IntegerKind.Usize 2));
      (uint_128_2,
        "into_limbs",
        Impl_ruint_Uint_BITS_LIMBS.into_limbs
          (Value.Integer IntegerKind.Usize 128)
          (Value.Integer IntegerKind.Usize 2));
      (uint_128_2,
        "as_limbs",
        Impl_ruint_Uint_BITS_LIMBS.as_limbs
          (Value.Integer IntegerKind.Usize 128)
          (Value.Integer IntegerKind.Usize 2));
      (uint_128_2,
        "as_limbs_mut",
        Impl_ruint_Uint_BITS_LIMBS.as_limbs_mut
          (Value.Integer IntegerKind.Usize 128)
          (Value.Integer IntegerKind.Usize 2))
    ]
    [
      ("core::convert::From",
        [ Ty.path "u64" ],
        Ty.path "u128",
        "from",
        convert.num.Impl_core_convert_From_u64_for_u128.from);
      ("core::iter::traits::collect::IntoIterator",
        [],
        range_usize,
        "into_iter",
        range_into_iter);
      ("core::iter::traits::iterator::Iterator",
        [],
        range_usize,
        "next",
        range_next);
      ("core::cmp::PartialEq",
        [ array_u64_2 ],
        array_u64_2,
        "eq",
        array_u64_eq);
      ("core::cmp::PartialEq",
        [ uint_128_2 ],
        uint_128_2,
        "eq",
        Impl_core_cmp_PartialEq_ruint_Uint_BITS_LIMBS_for_ruint_Uint_BITS_LIMBS.eq
          (Value.Integer IntegerKind.Usize 128)
          (Value.Integer IntegerKind.Usize 2));
      ("ruint::algorithms::DoubleWord",
        [ Ty.path "u64" ],
        Ty.path "u128",
        "low",
        algorithms.Impl_ruint_algorithms_DoubleWord_u64_for_u128.low);
      ("ruint::algorithms::DoubleWord",
        [ Ty.path "u64" ],
        Ty.path "u128",
        "high",
        algorithms.Impl_ruint_algorithms_DoubleWord_u64_for_u128.high);
      ("ruint::algorithms::DoubleWord",
        [ Ty.path "u64" ],
        Ty.path "u128",
        "split",
        algorithms.Impl_ruint_algorithms_DoubleWord_u64_for_u128.split)
    ].

Definition run_nlimbs (bits : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    Translated.Runtime.empty
    30
    (nlimbs [] [] [Value.Integer IntegerKind.Usize bits]).

Definition run_mask (bits : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    Translated.Runtime.empty
    100
    (mask [] [] [Value.Integer IntegerKind.Usize bits]).

Definition run_rem_up (a b : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    100
    (utils.rem_up
      []
      []
      [
        Value.Integer IntegerKind.Usize a;
        Value.Integer IntegerKind.Usize b
      ]).

Definition run_adc (lhs rhs carry : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    300
    (algorithms.ops.adc
      []
      []
      [
        Value.Integer IntegerKind.U64 lhs;
        Value.Integer IntegerKind.U64 rhs;
        Value.Integer IntegerKind.U64 carry
      ]).

Definition run_sbb (lhs rhs borrow : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    500
    (algorithms.ops.sbb
      []
      []
      [
        Value.Integer IntegerKind.U64 lhs;
        Value.Integer IntegerKind.U64 rhs;
        Value.Integer IntegerKind.U64 borrow
      ]).

Definition run_slice_len : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    100
    (M.let_
      (M.alloc
        slice_u64
        (Value.Array
          [
            Value.Integer IntegerKind.U64 10;
            Value.Integer IntegerKind.U64 20
          ]))
      (fun slice =>
        M.let_
          (M.get_associated_function slice_u64 "len" [] [])
          (fun len => M.call_closure (Ty.path "usize") len [ slice ]))).

Definition range_value (start end_ : Z) : Value.t :=
  Value.mkStructRecord
    "core::ops::range::Range"
    []
    [ Ty.path "usize" ]
    [
      ("start", Value.Integer IntegerKind.Usize start);
      ("end_", Value.Integer IntegerKind.Usize end_)
    ].

Definition run_range_into_iter : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    100
    (M.let_
      (M.get_trait_method
        "core::iter::traits::collect::IntoIterator"
        range_usize
        []
        []
        "into_iter"
        []
        [])
      (fun into_iter =>
        M.call_closure range_usize into_iter [ range_value 0 2 ])).

Definition run_range_next : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    100
    (M.let_
      (M.alloc range_usize (range_value 0 2))
      (fun range =>
        M.let_
          (M.get_trait_method
            "core::iter::traits::iterator::Iterator"
            range_usize
            []
            []
            "next"
            []
            [])
          (fun next =>
            M.call_closure
              (Ty.apply
                (Ty.path "core::option::Option")
                []
                [ Ty.path "usize" ])
              next
              [ range ]))).

Definition run_counting_loop : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    200
    (M.let_
      (M.alloc
        (Ty.path "usize")
        (Value.Integer IntegerKind.Usize 0))
      (fun counter =>
        M.let_
          (M.loop
            (Ty.tuple [])
            (M.let_
              (M.read counter)
              (fun value =>
                match value with
                | Value.Integer IntegerKind.Usize value =>
                  if Z.eqb value 3 then
                    M.break
                  else
                    M.let_
                      (M.write
                        counter
                        (Value.Integer IntegerKind.Usize (value + 1)))
                      (fun _ => M.alloc (Ty.tuple []) (Value.Tuple []))
                | _ => M.impossible "loop counter is not usize"
                end)))
          (fun _ => M.read counter))).

Definition uint_128_2_value (low high : Z) : Value.t :=
  Value.mkStructRecord
    "ruint::Uint"
    [
      Value.Integer IntegerKind.Usize 128;
      Value.Integer IntegerKind.Usize 2
    ]
    []
    [
      ("limbs",
        Value.Array
          [
            Value.Integer IntegerKind.U64 low;
            Value.Integer IntegerKind.U64 high
          ])
    ].

Definition run_uint_constant
    (name : string)
    (return_ty : Ty.t) :
    Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    1000
    (M.let_
      (get_associated_constant uint_128_2 name return_ty)
      M.read).

Definition run_uint_from_limbs (low high : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    1000
    (M.let_
      (M.get_associated_function uint_128_2 "from_limbs" [] [])
      (fun from_limbs =>
        M.call_closure
          uint_128_2
          from_limbs
          [
            Value.Array
              [
                Value.Integer IntegerKind.U64 low;
                Value.Integer IntegerKind.U64 high
              ]
          ])).

Definition run_uint_into_limbs (low high : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    500
    (M.let_
      (M.get_associated_function uint_128_2 "into_limbs" [] [])
      (fun into_limbs =>
        M.call_closure
          (Ty.apply
            (Ty.path "array")
            [ Value.Integer IntegerKind.Usize 2 ]
            [ Ty.path "u64" ])
          into_limbs
          [ uint_128_2_value low high ])).

Definition run_uint_as_limbs (low high : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    1000
    (M.let_
      (M.alloc uint_128_2 (uint_128_2_value low high))
      (fun self =>
        M.let_
          (M.get_associated_function uint_128_2 "as_limbs" [] [])
          (fun as_limbs =>
            M.let_
              (M.call_closure
                (Ty.apply
                  (Ty.path "&")
                  []
                  [
                    Ty.apply
                      (Ty.path "array")
                      [ Value.Integer IntegerKind.Usize 2 ]
                      [ Ty.path "u64" ]
                  ])
                as_limbs
                [ self ])
              M.read))).

Definition run_uint_as_limbs_mut (low high : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    1000
    (M.let_
      (M.alloc uint_128_2 (uint_128_2_value low high))
      (fun self =>
        M.let_
          (M.get_associated_function uint_128_2 "as_limbs_mut" [] [])
          (fun as_limbs_mut =>
            M.let_
              (M.call_closure
                (Ty.apply
                  (Ty.path "&mut")
                  []
                  [
                    Ty.apply
                      (Ty.path "array")
                      [ Value.Integer IntegerKind.Usize 2 ]
                      [ Ty.path "u64" ]
                  ])
                as_limbs_mut
                [ self ])
              M.read))).

Definition run_uint_as_limbs_mut_write
    (low high update : Z) :
    Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    1000
    (M.let_
      (M.alloc uint_128_2 (uint_128_2_value low high))
      (fun self =>
        M.let_
          (M.get_associated_function uint_128_2 "as_limbs_mut" [] [])
          (fun as_limbs_mut =>
            M.let_
              (M.call_closure
                (Ty.apply (Ty.path "&mut") [] [ array_u64_2 ])
                as_limbs_mut
                [ self ])
              (fun limbs =>
                M.let_
                  (M.SubPointer.get_array_field
                    limbs
                    (Value.Integer IntegerKind.Usize 1))
                  (fun high_limb =>
                    M.let_
                      (M.write
                        high_limb
                        (Value.Integer IntegerKind.U64 update))
                      (fun _ => M.read self)))))).

Definition run_uint_clone (low high : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    500
    (M.let_
      (M.alloc uint_128_2 (uint_128_2_value low high))
      (fun self =>
        Impl_core_clone_Clone_for_ruint_Uint_BITS_LIMBS.clone
          (Value.Integer IntegerKind.Usize 128)
          (Value.Integer IntegerKind.Usize 2)
          []
          []
          [ self ])).

Definition run_uint_default : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    500
    (Impl_core_default_Default_for_ruint_Uint_BITS_LIMBS.default
      (Value.Integer IntegerKind.Usize 128)
      (Value.Integer IntegerKind.Usize 2)
      []
      []
      []).

Definition run_uint_eq
    (lhs_low lhs_high rhs_low rhs_high : Z) :
    Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    1000
    (M.let_
      (M.alloc uint_128_2 (uint_128_2_value lhs_low lhs_high))
      (fun lhs =>
        M.let_
          (M.alloc uint_128_2 (uint_128_2_value rhs_low rhs_high))
          (fun rhs =>
            M.let_
              (M.get_trait_method
                "core::cmp::PartialEq"
                uint_128_2
                []
                [ uint_128_2 ]
                "eq"
                []
                [])
              (fun eq =>
                M.call_closure (Ty.path "bool") eq [ lhs; rhs ])))).

Definition run_double_word_join (high low : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    300
    (algorithms.Impl_ruint_algorithms_DoubleWord_u64_for_u128.join
      []
      []
      [ Value.Integer IntegerKind.U64 high; Value.Integer IntegerKind.U64 low ]).

Definition run_double_word_add (left right : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    300
    (algorithms.Impl_ruint_algorithms_DoubleWord_u64_for_u128.add
      []
      []
      [ Value.Integer IntegerKind.U64 left; Value.Integer IntegerKind.U64 right ]).

Definition run_double_word_mul (left right : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    300
    (algorithms.Impl_ruint_algorithms_DoubleWord_u64_for_u128.mul
      []
      []
      [ Value.Integer IntegerKind.U64 left; Value.Integer IntegerKind.U64 right ]).

Definition run_double_word_muladd (a b c : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    300
    (algorithms.Impl_ruint_algorithms_DoubleWord_u64_for_u128.muladd
      []
      []
      [
        Value.Integer IntegerKind.U64 a;
        Value.Integer IntegerKind.U64 b;
        Value.Integer IntegerKind.U64 c
      ]).

Definition run_double_word_muladd2 (a b c d : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    300
    (algorithms.Impl_ruint_algorithms_DoubleWord_u64_for_u128.muladd2
      []
      []
      [
        Value.Integer IntegerKind.U64 a;
        Value.Integer IntegerKind.U64 b;
        Value.Integer IntegerKind.U64 c;
        Value.Integer IntegerKind.U64 d
      ]).

Definition run_double_word_high (value : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    300
    (algorithms.Impl_ruint_algorithms_DoubleWord_u64_for_u128.high
      []
      []
      [ Value.Integer IntegerKind.U128 value ]).

Definition run_double_word_low (value : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    300
    (algorithms.Impl_ruint_algorithms_DoubleWord_u64_for_u128.low
      []
      []
      [ Value.Integer IntegerKind.U128 value ]).

Definition run_double_word_split (value : Z) : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    300
    (algorithms.Impl_ruint_algorithms_DoubleWord_u64_for_u128.split
      []
      []
      [ Value.Integer IntegerKind.U128 value ]).

Definition is_integer
    (kind : IntegerKind.t)
    (expected : Z)
    (result : Translated.Execution.t) :
    bool :=
  match result with
  | Translated.Execution.Done (inl (Value.Integer actual_kind actual)) =>
    andb (IntegerKind.eqb actual_kind kind) (Z.eqb actual expected)
  | _ => false
  end.

Definition is_bool
    (expected : bool)
    (result : Translated.Execution.t) :
    bool :=
  match result with
  | Translated.Execution.Done (inl (Value.Bool actual)) =>
    Bool.eqb actual expected
  | _ => false
  end.

Definition check_nlimbs (case : Z * Z) : bool :=
  let '(bits, expected) := case in
  is_integer IntegerKind.Usize expected (run_nlimbs bits).

Definition check_mask (case : Z * Z) : bool :=
  let '(bits, expected) := case in
  is_integer IntegerKind.U64 expected (run_mask bits).

Definition is_u64_pair
    (expected_low expected_high : Z)
    (result : Translated.Execution.t) :
    bool :=
  match result with
  | Translated.Execution.Done
      (inl
        (Value.Tuple
          [
            Value.Integer IntegerKind.U64 low;
            Value.Integer IntegerKind.U64 high
          ])) =>
    andb (Z.eqb low expected_low) (Z.eqb high expected_high)
  | _ => false
  end.

Definition is_u64_array2
    (expected_low expected_high : Z)
    (result : Translated.Execution.t) :
    bool :=
  match result with
  | Translated.Execution.Done
      (inl
        (Value.Array
          [
            Value.Integer IntegerKind.U64 low;
            Value.Integer IntegerKind.U64 high
          ])) =>
    andb (Z.eqb low expected_low) (Z.eqb high expected_high)
  | _ => false
  end.

Definition is_uint_128_2
    (expected_low expected_high : Z)
    (result : Translated.Execution.t) :
    bool :=
  match result with
  | Translated.Execution.Done
      (inl
        (Value.StructRecord
          constructor
          [
            Value.Integer IntegerKind.Usize bits;
            Value.Integer IntegerKind.Usize limbs
          ]
          []
          [
            (field,
              Value.Array
                [
                  Value.Integer IntegerKind.U64 low;
                  Value.Integer IntegerKind.U64 high
                ])
          ])) =>
    match PrimString.compare constructor "ruint::Uint",
      PrimString.compare field "limbs" with
    | Eq, Eq =>
      andb
        (andb (Z.eqb bits 128) (Z.eqb limbs 2))
        (andb (Z.eqb low expected_low) (Z.eqb high expected_high))
    | _, _ => false
    end
  | _ => false
  end.

Definition check_adc (case : (Z * Z * Z) * (Z * Z)) : bool :=
  let '((lhs, rhs, carry), (expected_low, expected_high)) := case in
  is_u64_pair expected_low expected_high (run_adc lhs rhs carry).

Definition check_sbb (case : (Z * Z * Z) * (Z * Z)) : bool :=
  let '((lhs, rhs, borrow), (expected_low, expected_high)) := case in
  is_u64_pair expected_low expected_high (run_sbb lhs rhs borrow).

Definition is_usize_some
    (expected : Z)
    (result : Translated.Execution.t) :
    bool :=
  match result with
  | Translated.Execution.Done
      (inl
        (Value.StructTuple
          constructor
          []
          [ ty ]
          [ Value.Integer IntegerKind.Usize actual ])) =>
    match PrimString.compare constructor "core::option::Option::Some" with
    | Eq => andb (Translated.ty_eqb ty (Ty.path "usize")) (Z.eqb actual expected)
    | _ => false
    end
  | _ => false
  end.

Definition range_helpers_failure : option (Z * Translated.Execution.t) :=
  if is_integer IntegerKind.Usize 2 run_slice_len then
    match run_range_into_iter with
    | Translated.Execution.Done (inl (Value.StructRecord _ _ _ _)) =>
      if is_usize_some 0 run_range_next then
        if is_integer IntegerKind.Usize 3 run_counting_loop then
          None
        else
          Some (-13, run_counting_loop)
      else
        Some (-12, run_range_next)
    | result => Some (-11, result)
    end
  else
    Some (-10, run_slice_len).

Definition double_word_cases_pass : bool :=
  List.forallb
    id
    [
      is_integer
        IntegerKind.U128
        18446744073709551618
        (run_double_word_join 1 2);
      is_integer
        IntegerKind.U128
        36893488147419103230
        (run_double_word_add 18446744073709551615 18446744073709551615);
      is_integer
        IntegerKind.U128
        340282366920938463426481119284349108225
        (run_double_word_mul 18446744073709551615 18446744073709551615);
      is_integer
        IntegerKind.U128
        340282366920938463444927863358058659840
        (run_double_word_muladd
          18446744073709551615
          18446744073709551615
          18446744073709551615);
      is_integer
        IntegerKind.U128
        340282366920938463463374607431768211455
        (run_double_word_muladd2
          18446744073709551615
          18446744073709551615
          18446744073709551615
          18446744073709551615);
      is_integer
        IntegerKind.U64
        1
        (run_double_word_high 18446744073709551618);
      is_integer
        IntegerKind.U64
        2
        (run_double_word_low 18446744073709551618);
      is_u64_pair 2 1 (run_double_word_split 18446744073709551618)
    ].

Definition uint_cases_pass : bool :=
  List.forallb
    id
    [
      is_integer
        IntegerKind.Usize
        128
        (run_uint_constant "BITS" (Ty.path "usize"));
      is_integer
        IntegerKind.Usize
        2
        (run_uint_constant "LIMBS" (Ty.path "usize"));
      is_integer
        IntegerKind.U64
        18446744073709551615
        (run_uint_constant "MASK" (Ty.path "u64"));
      is_uint_128_2 0 0 (run_uint_constant "ZERO" uint_128_2);
      is_uint_128_2 0 0 (run_uint_constant "MIN" uint_128_2);
      is_uint_128_2
        18446744073709551615
        18446744073709551615
        (run_uint_constant "MAX" uint_128_2);
      is_uint_128_2 11 22 (run_uint_from_limbs 11 22);
      is_u64_array2 11 22 (run_uint_into_limbs 11 22);
      is_u64_array2 11 22 (run_uint_as_limbs 11 22);
      is_u64_array2 11 22 (run_uint_as_limbs_mut 11 22);
      is_uint_128_2 11 99 (run_uint_as_limbs_mut_write 11 22 99);
      is_uint_128_2 11 22 (run_uint_clone 11 22);
      is_uint_128_2 0 0 run_uint_default;
      is_bool true (run_uint_eq 11 22 11 22);
      is_bool false (run_uint_eq 11 22 11 23)
    ].

Definition uint_extended_failure : option (Z * Translated.Execution.t) :=
  let mut_write := run_uint_as_limbs_mut_write 11 22 99 in
  if is_uint_128_2 11 99 mut_write then
    let clone := run_uint_clone 11 22 in
    if is_uint_128_2 11 22 clone then
      if is_uint_128_2 0 0 run_uint_default then
        let equal := run_uint_eq 11 22 11 22 in
        if is_bool true equal then
          let unequal := run_uint_eq 11 22 11 23 in
          if is_bool false unequal then None else Some (-25, unequal)
        else
          Some (-24, equal)
      else
        Some (-23, run_uint_default)
    else
      Some (-22, clone)
  else
    Some (-21, mut_write).

Definition nlimbs_cases : list (Z * Z) :=
  [
    (0, 0);
    (1, 1);
    (63, 1);
    (64, 1);
    (65, 2);
    (127, 2);
    (128, 2);
    (129, 3);
    (255, 4);
    (256, 4);
    (257, 5)
  ].

Definition mask_cases : list (Z * Z) :=
  [
    (0, 0);
    (1, 1);
    (2, 3);
    (7, 127);
    (8, 255);
    (32, 4294967295);
    (63, 9223372036854775807);
    (64, 18446744073709551615);
    (65, 1)
  ].

Definition rem_up_cases_pass : bool :=
  List.forallb
    id
    [
      is_integer IntegerKind.Usize 1 (run_rem_up 10 3);
      is_integer IntegerKind.Usize 3 (run_rem_up 9 3);
      is_integer IntegerKind.Usize 4 (run_rem_up 4 8);
      is_integer IntegerKind.Usize 64 (run_rem_up 128 64)
    ].

Definition adc_cases : list ((Z * Z * Z) * (Z * Z)) :=
  [
    ((1, 2, 3), (6, 0));
    ((18446744073709551615, 1, 0), (0, 1));
    ((18446744073709551615, 18446744073709551615, 1),
      (18446744073709551615, 1))
  ].

Definition sbb_cases : list ((Z * Z * Z) * (Z * Z)) :=
  [
    ((5, 3, 1), (1, 0));
    ((0, 1, 0), (18446744073709551615, 1));
    ((0, 0, 1), (18446744073709551615, 1));
    ((18446744073709551615, 0, 0), (18446744073709551615, 0))
  ].

Fixpoint first_failed_mask
    (cases : list (Z * Z)) :
    option (Z * Translated.Execution.t) :=
  match cases with
  | [] => None
  | (bits, expected) :: cases =>
    let result := run_mask bits in
    if is_integer IntegerKind.U64 expected result then
      first_failed_mask cases
    else
      Some (bits, result)
  end.

Fixpoint first_failed_adc
    (cases : list ((Z * Z * Z) * (Z * Z)))
    (index : Z) :
    option (Z * Translated.Execution.t) :=
  match cases with
  | [] => None
  | ((lhs, rhs, carry), (expected_low, expected_high)) :: cases =>
    let result := run_adc lhs rhs carry in
    if is_u64_pair expected_low expected_high result then
      first_failed_adc cases (index + 1)
    else
      Some (index, result)
  end.

Fixpoint first_failed_sbb
    (cases : list ((Z * Z * Z) * (Z * Z)))
    (index : Z) :
    option (Z * Translated.Execution.t) :=
  match cases with
  | [] => None
  | ((lhs, rhs, borrow), (expected_low, expected_high)) :: cases =>
    let result := run_sbb lhs rhs borrow in
    if is_u64_pair expected_low expected_high result then
      first_failed_sbb cases (index + 1)
    else
      Some (index, result)
  end.

Definition first_failure : option (Z * Translated.Execution.t) :=
  match range_helpers_failure with
  | Some failure => Some failure
  | None =>
    match uint_extended_failure with
    | Some failure => Some failure
    | None =>
      if rem_up_cases_pass then
      if uint_cases_pass then
      if double_word_cases_pass then
      if List.forallb check_nlimbs nlimbs_cases then
        match first_failed_mask mask_cases with
        | Some failure => Some failure
        | None =>
          match first_failed_adc adc_cases 0 with
          | Some failure => Some failure
          | None => first_failed_sbb sbb_cases 0
          end
        end
      else
        Some (-1, Translated.Execution.Unsupported "nlimbs case failed")
      else
        Some (-2, Translated.Execution.Unsupported "DoubleWord case failed")
    else
      Some (-3, Translated.Execution.Unsupported "Uint case failed")
    else
      Some (-4, Translated.Execution.Unsupported "rem_up case failed")
    end
  end.

Parameter assert_none : option (Z * Translated.Execution.t) -> unit.

Definition main : unit :=
  assert_none first_failure.

Extract Constant assert_none =>
  "(function
    | None -> ()
    | Some (bits, Translated.Execution.Unsupported message) ->
      failwith
        (""ruint arithmetic stopped at "" ^ Big_int_Z.string_of_big_int bits ^
          "": "" ^ Pstring.to_string message)
    | Some (bits, Translated.Execution.OutOfFuel) ->
      failwith (""ruint arithmetic ran out of fuel at "" ^ Big_int_Z.string_of_big_int bits)
    | Some (bits, Translated.Execution.Done (Inl (Value.Integer (_, actual)))) ->
      failwith
        (""ruint arithmetic failed at "" ^ Big_int_Z.string_of_big_int bits ^
          "" with "" ^ Big_int_Z.string_of_big_int actual)
    | Some (bits, Translated.Execution.Done _) ->
      failwith
        (""ruint arithmetic returned an unexpected value at "" ^
          Big_int_Z.string_of_big_int bits))".

Set Extraction Output Directory "evaluate/extracted".
Extraction "ruint.ml" main.
