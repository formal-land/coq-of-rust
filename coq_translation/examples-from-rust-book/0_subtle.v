Definition Choice : Set :=
  u8.

(* Impl [Choice] *)
  
(* End impl [Choice] *)

(* Impl [Choice] *)
  Definition clone (self : ref Self) : Choice :=
    let _ := tt in
    deref self.
(* End impl [Choice] *)

(* Impl [Choice] *)
  Definition fmt
    (self : ref Self)
    (f : ref $crate.fmt.Formatter)
    : $crate.fmt.Result :=
    debug_tuple_field1_finish f "Choice" self.0.
(* End impl [Choice] *)

(* Impl [Choice] *)
  Definition unwrap_u8 (self : ref Self) : u8 :=
    self.0.
(* End impl [Choice] *)

(* Impl [bool] *)
  Definition from (source : Choice) : bool :=
    if true then
      if not (bit_and (eq source.0 0) (eq source.0 1)) then
        $crate.panicking.panic "assertion failed: (source.0 == 0u8) | (source.0 == 1u8)"
      else
        tt ;;
      tt
    else
      tt ;;
    ne source.0 0.
(* End impl [bool] *)

(* Impl [Choice] *)
  Definition Output : Set :=
    Choice.
  
  Definition bitand (self : Self) (rhs : Choice) : Choice :=
    (bit_and self.0 rhs.0) .
(* End impl [Choice] *)

(* Impl [Choice] *)
  Definition bitand_assign (self : ref Self) (rhs : Choice) :=
    assign deref self := bit_and (deref self) rhs ;;
    tt.
(* End impl [Choice] *)

(* Impl [Choice] *)
  Definition Output : Set :=
    Choice.
  
  Definition bitor (self : Self) (rhs : Choice) : Choice :=
    (bit_and self.0 rhs.0) .
(* End impl [Choice] *)

(* Impl [Choice] *)
  Definition bitor_assign (self : ref Self) (rhs : Choice) :=
    assign deref self := bit_and (deref self) rhs ;;
    tt.
(* End impl [Choice] *)

(* Impl [Choice] *)
  Definition Output : Set :=
    Choice.
  
  Definition bitxor (self : Self) (rhs : Choice) : Choice :=
    (bit_xor self.0 rhs.0) .
(* End impl [Choice] *)

(* Impl [Choice] *)
  Definition bitxor_assign (self : ref Self) (rhs : Choice) :=
    assign deref self := bit_xor (deref self) rhs ;;
    tt.
(* End impl [Choice] *)

(* Impl [Choice] *)
  Definition Output : Set :=
    Choice.
  
  Definition not (self : Self) : Choice :=
    (bit_and 1 (not self.0)) .
(* End impl [Choice] *)

Definition black_box :=
  if true then
    if not (bit_and (eq input 0) (eq input 1)) then
      $crate.panicking.panic "assertion failed: (input == 0u8) | (input == 1u8)"
    else
      tt ;;
    tt
  else
    tt ;;
  core.ptr.read_volatile input.

(* Impl [Choice] *)
  Definition from (input : u8) : Choice :=
    Choice (black_box input).
(* End impl [Choice] *)

Error Trait.

(* Impl [Slice] *)
  Definition ct_eq (self : ref Self) (_rhs : ref Slice) : Choice :=
    let len := self  in
    if ne len (_rhs ) then
      Return (from 0) ;;
      tt
    else
      tt ;;
    let x := 1 in
    match into_iter ((self ) (_rhs )) with
    | iter =>
      loop match next iter with
      | None [] => Break
      | Some [0 : (ai, bi)] =>
        assign x := x bit_and (ai bi)  ;;
        tt
      end ;;
      tt from for
    end ;;
    x .
(* End impl [Slice] *)

(* Impl [Choice] *)
  Definition ct_eq (self : ref Self) (rhs : ref Choice) : Choice :=
    not (bit_xor (deref self) (deref rhs)).
(* End impl [Choice] *)

(* Impl [u8] *)
  Definition ct_eq (self : ref Self) (other : ref u8) : Choice :=
    let x := bit_xor self other in
    let y := shr (bit_and x (x )) (sub 8 1) in
    (bit_xor y 1) .
(* End impl [u8] *)

(* Impl [i8] *)
  Definition ct_eq (self : ref Self) (other : ref i8) : Choice :=
    (deref self) (deref other).
(* End impl [i8] *)

(* Impl [u16] *)
  Definition ct_eq (self : ref Self) (other : ref u16) : Choice :=
    let x := bit_xor self other in
    let y := shr (bit_and x (x )) (sub 16 1) in
    (bit_xor y 1) .
(* End impl [u16] *)

(* Impl [i16] *)
  Definition ct_eq (self : ref Self) (other : ref i16) : Choice :=
    (deref self) (deref other).
(* End impl [i16] *)

(* Impl [u32] *)
  Definition ct_eq (self : ref Self) (other : ref u32) : Choice :=
    let x := bit_xor self other in
    let y := shr (bit_and x (x )) (sub 32 1) in
    (bit_xor y 1) .
(* End impl [u32] *)

(* Impl [i32] *)
  Definition ct_eq (self : ref Self) (other : ref i32) : Choice :=
    (deref self) (deref other).
(* End impl [i32] *)

(* Impl [u64] *)
  Definition ct_eq (self : ref Self) (other : ref u64) : Choice :=
    let x := bit_xor self other in
    let y := shr (bit_and x (x )) (sub 64 1) in
    (bit_xor y 1) .
(* End impl [u64] *)

(* Impl [i64] *)
  Definition ct_eq (self : ref Self) (other : ref i64) : Choice :=
    (deref self) (deref other).
(* End impl [i64] *)

(* Impl [usize] *)
  Definition ct_eq (self : ref Self) (other : ref usize) : Choice :=
    let x := bit_xor self other in
    let y := shr (bit_and x (x )) (sub (mul ({{root}}.core.mem.size_of ) 8) 1) in
    (bit_xor y 1) .
(* End impl [usize] *)

(* Impl [isize] *)
  Definition ct_eq (self : ref Self) (other : ref isize) : Choice :=
    (deref self) (deref other).
(* End impl [isize] *)

Error Trait.

(* Impl [u8] *)
  Definition conditional_select
    (a : ref Self)
    (b : ref Self)
    (choice : Choice)
    : Self :=
    let mask := neg (choice ) in
    bit_xor a (bit_and mask (bit_xor a b)).
  
  Definition conditional_assign
    (self : ref Self)
    (other : ref Self)
    (choice : Choice) :=
    let mask := neg (choice ) in
    assign deref self := deref self bit_xor bit_and mask (bit_xor (deref self) (deref other)) ;;
    tt.
  
  Definition conditional_swap (a : ref Self) (b : ref Self) (choice : Choice) :=
    let mask := neg (choice ) in
    let t := bit_and mask (bit_xor (deref a) (deref b)) in
    assign deref a := deref a bit_xor t ;;
    assign deref b := deref b bit_xor t ;;
    tt.
(* End impl [u8] *)

(* Impl [i8] *)
  Definition conditional_select
    (a : ref Self)
    (b : ref Self)
    (choice : Choice)
    : Self :=
    let mask := neg (choice ) in
    bit_xor a (bit_and mask (bit_xor a b)).
  
  Definition conditional_assign
    (self : ref Self)
    (other : ref Self)
    (choice : Choice) :=
    let mask := neg (choice ) in
    assign deref self := deref self bit_xor bit_and mask (bit_xor (deref self) (deref other)) ;;
    tt.
  
  Definition conditional_swap (a : ref Self) (b : ref Self) (choice : Choice) :=
    let mask := neg (choice ) in
    let t := bit_and mask (bit_xor (deref a) (deref b)) in
    assign deref a := deref a bit_xor t ;;
    assign deref b := deref b bit_xor t ;;
    tt.
(* End impl [i8] *)

(* Impl [u16] *)
  Definition conditional_select
    (a : ref Self)
    (b : ref Self)
    (choice : Choice)
    : Self :=
    let mask := neg (choice ) in
    bit_xor a (bit_and mask (bit_xor a b)).
  
  Definition conditional_assign
    (self : ref Self)
    (other : ref Self)
    (choice : Choice) :=
    let mask := neg (choice ) in
    assign deref self := deref self bit_xor bit_and mask (bit_xor (deref self) (deref other)) ;;
    tt.
  
  Definition conditional_swap (a : ref Self) (b : ref Self) (choice : Choice) :=
    let mask := neg (choice ) in
    let t := bit_and mask (bit_xor (deref a) (deref b)) in
    assign deref a := deref a bit_xor t ;;
    assign deref b := deref b bit_xor t ;;
    tt.
(* End impl [u16] *)

(* Impl [i16] *)
  Definition conditional_select
    (a : ref Self)
    (b : ref Self)
    (choice : Choice)
    : Self :=
    let mask := neg (choice ) in
    bit_xor a (bit_and mask (bit_xor a b)).
  
  Definition conditional_assign
    (self : ref Self)
    (other : ref Self)
    (choice : Choice) :=
    let mask := neg (choice ) in
    assign deref self := deref self bit_xor bit_and mask (bit_xor (deref self) (deref other)) ;;
    tt.
  
  Definition conditional_swap (a : ref Self) (b : ref Self) (choice : Choice) :=
    let mask := neg (choice ) in
    let t := bit_and mask (bit_xor (deref a) (deref b)) in
    assign deref a := deref a bit_xor t ;;
    assign deref b := deref b bit_xor t ;;
    tt.
(* End impl [i16] *)

(* Impl [u32] *)
  Definition conditional_select
    (a : ref Self)
    (b : ref Self)
    (choice : Choice)
    : Self :=
    let mask := neg (choice ) in
    bit_xor a (bit_and mask (bit_xor a b)).
  
  Definition conditional_assign
    (self : ref Self)
    (other : ref Self)
    (choice : Choice) :=
    let mask := neg (choice ) in
    assign deref self := deref self bit_xor bit_and mask (bit_xor (deref self) (deref other)) ;;
    tt.
  
  Definition conditional_swap (a : ref Self) (b : ref Self) (choice : Choice) :=
    let mask := neg (choice ) in
    let t := bit_and mask (bit_xor (deref a) (deref b)) in
    assign deref a := deref a bit_xor t ;;
    assign deref b := deref b bit_xor t ;;
    tt.
(* End impl [u32] *)

(* Impl [i32] *)
  Definition conditional_select
    (a : ref Self)
    (b : ref Self)
    (choice : Choice)
    : Self :=
    let mask := neg (choice ) in
    bit_xor a (bit_and mask (bit_xor a b)).
  
  Definition conditional_assign
    (self : ref Self)
    (other : ref Self)
    (choice : Choice) :=
    let mask := neg (choice ) in
    assign deref self := deref self bit_xor bit_and mask (bit_xor (deref self) (deref other)) ;;
    tt.
  
  Definition conditional_swap (a : ref Self) (b : ref Self) (choice : Choice) :=
    let mask := neg (choice ) in
    let t := bit_and mask (bit_xor (deref a) (deref b)) in
    assign deref a := deref a bit_xor t ;;
    assign deref b := deref b bit_xor t ;;
    tt.
(* End impl [i32] *)

(* Impl [u64] *)
  Definition conditional_select
    (a : ref Self)
    (b : ref Self)
    (choice : Choice)
    : Self :=
    let mask := neg (choice ) in
    bit_xor a (bit_and mask (bit_xor a b)).
  
  Definition conditional_assign
    (self : ref Self)
    (other : ref Self)
    (choice : Choice) :=
    let mask := neg (choice ) in
    assign deref self := deref self bit_xor bit_and mask (bit_xor (deref self) (deref other)) ;;
    tt.
  
  Definition conditional_swap (a : ref Self) (b : ref Self) (choice : Choice) :=
    let mask := neg (choice ) in
    let t := bit_and mask (bit_xor (deref a) (deref b)) in
    assign deref a := deref a bit_xor t ;;
    assign deref b := deref b bit_xor t ;;
    tt.
(* End impl [u64] *)

(* Impl [i64] *)
  Definition conditional_select
    (a : ref Self)
    (b : ref Self)
    (choice : Choice)
    : Self :=
    let mask := neg (choice ) in
    bit_xor a (bit_and mask (bit_xor a b)).
  
  Definition conditional_assign
    (self : ref Self)
    (other : ref Self)
    (choice : Choice) :=
    let mask := neg (choice ) in
    assign deref self := deref self bit_xor bit_and mask (bit_xor (deref self) (deref other)) ;;
    tt.
  
  Definition conditional_swap (a : ref Self) (b : ref Self) (choice : Choice) :=
    let mask := neg (choice ) in
    let t := bit_and mask (bit_xor (deref a) (deref b)) in
    assign deref a := deref a bit_xor t ;;
    assign deref b := deref b bit_xor t ;;
    tt.
(* End impl [i64] *)

(* Impl [Choice] *)
  Definition conditional_select
    (a : ref Self)
    (b : ref Self)
    (choice : Choice)
    : Self :=
    Choice (conditional_select a.0 b.0 choice).
(* End impl [Choice] *)

Error Trait.

(* Impl [T] *)
  Definition conditional_negate (self : ref Self) (choice : Choice) :=
    let self_neg := neg self in
    self self_neg choice ;;
    tt.
(* End impl [T] *)

Error Struct.

(* Impl [CtOption] *)
  Definition clone (self : ref Self) : CtOption :=
    struct CtOption {value := $crate.clone.Clone.clone self.value;is_some := $crate.clone.Clone.clone self.is_some} .
(* End impl [CtOption] *)

(* Impl [CtOption] *)
  
(* End impl [CtOption] *)

(* Impl [CtOption] *)
  Definition fmt
    (self : ref Self)
    (f : ref $crate.fmt.Formatter)
    : $crate.fmt.Result :=
    debug_struct_field2_finish f "CtOption" "value" self.value "is_some" self.is_some.
(* End impl [CtOption] *)

(* Impl [Option] *)
  Definition from (source : CtOption) : Option :=
    if eq ((source ) ) 1 then
      Option.Some source.value
    else
      None.
(* End impl [Option] *)

(* Impl [CtOption] *)
  Definition new (value : T) (is_some : Choice) : CtOption :=
    struct CtOption {value := value;is_some := is_some} .
  
  Definition expect (self : Self) (msg : ref str) : T :=
    match (self.is_some , 1) with
    | (left_val, right_val) =>
      if not (eq (deref left_val) (deref right_val)) then
        let kind := $crate.panicking.AssertKind.Eq in
        $crate.panicking.assert_failed kind (deref left_val) (deref right_val) ($crate.option.Option.Some (new_v1 [""] [new_display msg])) ;;
        tt
      else
        tt
    end ;;
    self.value.
  
  Definition unwrap (self : Self) : T :=
    match (self.is_some , 1) with
    | (left_val, right_val) =>
      if not (eq (deref left_val) (deref right_val)) then
        let kind := $crate.panicking.AssertKind.Eq in
        $crate.panicking.assert_failed kind (deref left_val) (deref right_val) $crate.option.Option.None ;;
        tt
      else
        tt
    end ;;
    self.value.
  
  Definition unwrap_or (self : Self) (def : T) : T :=
    conditional_select def self.value self.is_some.
  
  Definition unwrap_or_else (self : Self) (f : F) : T :=
    conditional_select (f ) self.value self.is_some.
  
  Definition is_some (self : ref Self) : Choice :=
    self.is_some.
  
  Definition is_none (self : ref Self) : Choice :=
    not self.is_some.
  
  Definition map (self : Self) (f : F) : CtOption :=
    new (f (conditional_select (default ) self.value self.is_some)) self.is_some.
  
  Definition and_then (self : Self) (f : F) : CtOption :=
    let tmp := f (conditional_select (default ) self.value self.is_some) in
    assign tmp.is_some := tmp.is_some bit_and self.is_some ;;
    tmp.
  
  Definition or_else (self : Self) (f : F) : CtOption :=
    let is_none := self  in
    let f := f  in
    conditional_select self f is_none.
(* End impl [CtOption] *)

(* Impl [CtOption] *)
  Definition conditional_select
    (a : ref Self)
    (b : ref Self)
    (choice : Choice)
    : Self :=
    new (conditional_select a.value b.value choice) (conditional_select a.is_some b.is_some choice).
(* End impl [CtOption] *)

(* Impl [CtOption] *)
  Definition ct_eq (self : ref Self) (rhs : ref CtOption) : Choice :=
    let a := self  in
    let b := rhs  in
    bit_and (bit_and (bit_and a b) (self.value rhs.value)) (bit_and (not a) (not b)).
(* End impl [CtOption] *)

Error Trait.

(* Impl [u8] *)
  Definition ct_gt (self : ref Self) (other : ref u8) : Choice :=
    let gtb := bit_and self (not other) in
    let ltb := bit_and (not self) other in
    let pow := 1 in
    loop (if lt pow 8 then
      assign ltb := ltb bit_and shr ltb pow ;;
      assign pow := pow add pow ;;
      tt
    else
      Break ;;
      tt) from while ;;
    let bit := bit_and gtb (not ltb) in
    let pow := 1 in
    loop (if lt pow 8 then
      assign bit := bit bit_and shr bit pow ;;
      assign pow := pow add pow ;;
      tt
    else
      Break ;;
      tt) from while ;;
    from (bit_and bit 1).
(* End impl [u8] *)

(* Impl [u16] *)
  Definition ct_gt (self : ref Self) (other : ref u16) : Choice :=
    let gtb := bit_and self (not other) in
    let ltb := bit_and (not self) other in
    let pow := 1 in
    loop (if lt pow 16 then
      assign ltb := ltb bit_and shr ltb pow ;;
      assign pow := pow add pow ;;
      tt
    else
      Break ;;
      tt) from while ;;
    let bit := bit_and gtb (not ltb) in
    let pow := 1 in
    loop (if lt pow 16 then
      assign bit := bit bit_and shr bit pow ;;
      assign pow := pow add pow ;;
      tt
    else
      Break ;;
      tt) from while ;;
    from (bit_and bit 1).
(* End impl [u16] *)

(* Impl [u32] *)
  Definition ct_gt (self : ref Self) (other : ref u32) : Choice :=
    let gtb := bit_and self (not other) in
    let ltb := bit_and (not self) other in
    let pow := 1 in
    loop (if lt pow 32 then
      assign ltb := ltb bit_and shr ltb pow ;;
      assign pow := pow add pow ;;
      tt
    else
      Break ;;
      tt) from while ;;
    let bit := bit_and gtb (not ltb) in
    let pow := 1 in
    loop (if lt pow 32 then
      assign bit := bit bit_and shr bit pow ;;
      assign pow := pow add pow ;;
      tt
    else
      Break ;;
      tt) from while ;;
    from (bit_and bit 1).
(* End impl [u32] *)

(* Impl [u64] *)
  Definition ct_gt (self : ref Self) (other : ref u64) : Choice :=
    let gtb := bit_and self (not other) in
    let ltb := bit_and (not self) other in
    let pow := 1 in
    loop (if lt pow 64 then
      assign ltb := ltb bit_and shr ltb pow ;;
      assign pow := pow add pow ;;
      tt
    else
      Break ;;
      tt) from while ;;
    let bit := bit_and gtb (not ltb) in
    let pow := 1 in
    loop (if lt pow 64 then
      assign bit := bit bit_and shr bit pow ;;
      assign pow := pow add pow ;;
      tt
    else
      Break ;;
      tt) from while ;;
    from (bit_and bit 1).
(* End impl [u64] *)

Error Trait.

(* Impl [u8] *)
  
(* End impl [u8] *)

(* Impl [u16] *)
  
(* End impl [u16] *)

(* Impl [u32] *)
  
(* End impl [u32] *)

(* Impl [u64] *)
  
(* End impl [u64] *)