Definition Choice : Set :=
  u8.

Definition clone :=
  let _ := tt in
  unary self.

Definition fmt :=
  debug_tuple_field1_finish f "Choice" self.0.

Definition unwrap_u8 :=
  self.0.

Definition from :=
  if true then
    if unary (bit_and (eq source.0 0) (eq source.0 1)) then
      $crate.panicking.panic "assertion failed: (source.0 == 0u8) | (source.0 == 1u8)"
    else
      tt ;;
    tt
  else
    tt ;;
  ne source.0 0.

Error ImplItemKind::Type.

Definition bitand :=
  (bit_and self.0 rhs.0) .

Definition bitand_assign :=
  assign unary self := bit_and (unary self) rhs ;;
  tt.

Error ImplItemKind::Type.

Definition bitor :=
  (bit_and self.0 rhs.0) .

Definition bitor_assign :=
  assign unary self := bit_and (unary self) rhs ;;
  tt.

Error ImplItemKind::Type.

Definition bitxor :=
  (bit_xor self.0 rhs.0) .

Definition bitxor_assign :=
  assign unary self := bit_xor (unary self) rhs ;;
  tt.

Error ImplItemKind::Type.

Definition not :=
  (bit_and 1 (unary self.0)) .

Definition black_box :=
  if true then
    if unary (bit_and (eq input 0) (eq input 1)) then
      $crate.panicking.panic "assertion failed: (input == 0u8) | (input == 1u8)"
    else
      tt ;;
    tt
  else
    tt ;;
  core.ptr.read_volatile input.

Definition from :=
  Choice (black_box input).

Error Trait.

Definition ct_eq :=
  let len := self  in
  if ne len (_rhs ) then
    Return (from 0) ;;
    tt
  else
    tt ;;
  let x := 1 in
  match into_iter ((self ) (_rhs )) with iter => loop match next iter with None [] => Break Some [0 : (ai,bi)] => assign x := x bit_and (ai bi)  ;;
  tt end ;;
  tt from for end ;;
  x .

Definition ct_eq :=
  unary (bit_xor (unary self) (unary rhs)).

Definition ct_eq :=
  let x := bit_xor self other in
  let y := shr (bit_and x (x )) (sub 8 1) in
  (bit_xor y 1) .

Definition ct_eq :=
  (unary self) (unary other).

Definition ct_eq :=
  let x := bit_xor self other in
  let y := shr (bit_and x (x )) (sub 16 1) in
  (bit_xor y 1) .

Definition ct_eq :=
  (unary self) (unary other).

Definition ct_eq :=
  let x := bit_xor self other in
  let y := shr (bit_and x (x )) (sub 32 1) in
  (bit_xor y 1) .

Definition ct_eq :=
  (unary self) (unary other).

Definition ct_eq :=
  let x := bit_xor self other in
  let y := shr (bit_and x (x )) (sub 64 1) in
  (bit_xor y 1) .

Definition ct_eq :=
  (unary self) (unary other).

Definition ct_eq :=
  let x := bit_xor self other in
  let y := shr (bit_and x (x )) (sub (mul ({{root}}.core.mem.size_of ) 8) 1) in
  (bit_xor y 1) .

Definition ct_eq :=
  (unary self) (unary other).

Error Trait.

Definition conditional_select :=
  let mask := unary (choice ) in
  bit_xor a (bit_and mask (bit_xor a b)).

Definition conditional_assign :=
  let mask := unary (choice ) in
  assign unary self := unary self bit_xor bit_and mask (bit_xor (unary self) (unary other)) ;;
  tt.

Definition conditional_swap :=
  let mask := unary (choice ) in
  let t := bit_and mask (bit_xor (unary a) (unary b)) in
  assign unary a := unary a bit_xor t ;;
  assign unary b := unary b bit_xor t ;;
  tt.

Definition conditional_select :=
  let mask := unary (choice ) in
  bit_xor a (bit_and mask (bit_xor a b)).

Definition conditional_assign :=
  let mask := unary (choice ) in
  assign unary self := unary self bit_xor bit_and mask (bit_xor (unary self) (unary other)) ;;
  tt.

Definition conditional_swap :=
  let mask := unary (choice ) in
  let t := bit_and mask (bit_xor (unary a) (unary b)) in
  assign unary a := unary a bit_xor t ;;
  assign unary b := unary b bit_xor t ;;
  tt.

Definition conditional_select :=
  let mask := unary (choice ) in
  bit_xor a (bit_and mask (bit_xor a b)).

Definition conditional_assign :=
  let mask := unary (choice ) in
  assign unary self := unary self bit_xor bit_and mask (bit_xor (unary self) (unary other)) ;;
  tt.

Definition conditional_swap :=
  let mask := unary (choice ) in
  let t := bit_and mask (bit_xor (unary a) (unary b)) in
  assign unary a := unary a bit_xor t ;;
  assign unary b := unary b bit_xor t ;;
  tt.

Definition conditional_select :=
  let mask := unary (choice ) in
  bit_xor a (bit_and mask (bit_xor a b)).

Definition conditional_assign :=
  let mask := unary (choice ) in
  assign unary self := unary self bit_xor bit_and mask (bit_xor (unary self) (unary other)) ;;
  tt.

Definition conditional_swap :=
  let mask := unary (choice ) in
  let t := bit_and mask (bit_xor (unary a) (unary b)) in
  assign unary a := unary a bit_xor t ;;
  assign unary b := unary b bit_xor t ;;
  tt.

Definition conditional_select :=
  let mask := unary (choice ) in
  bit_xor a (bit_and mask (bit_xor a b)).

Definition conditional_assign :=
  let mask := unary (choice ) in
  assign unary self := unary self bit_xor bit_and mask (bit_xor (unary self) (unary other)) ;;
  tt.

Definition conditional_swap :=
  let mask := unary (choice ) in
  let t := bit_and mask (bit_xor (unary a) (unary b)) in
  assign unary a := unary a bit_xor t ;;
  assign unary b := unary b bit_xor t ;;
  tt.

Definition conditional_select :=
  let mask := unary (choice ) in
  bit_xor a (bit_and mask (bit_xor a b)).

Definition conditional_assign :=
  let mask := unary (choice ) in
  assign unary self := unary self bit_xor bit_and mask (bit_xor (unary self) (unary other)) ;;
  tt.

Definition conditional_swap :=
  let mask := unary (choice ) in
  let t := bit_and mask (bit_xor (unary a) (unary b)) in
  assign unary a := unary a bit_xor t ;;
  assign unary b := unary b bit_xor t ;;
  tt.

Definition conditional_select :=
  let mask := unary (choice ) in
  bit_xor a (bit_and mask (bit_xor a b)).

Definition conditional_assign :=
  let mask := unary (choice ) in
  assign unary self := unary self bit_xor bit_and mask (bit_xor (unary self) (unary other)) ;;
  tt.

Definition conditional_swap :=
  let mask := unary (choice ) in
  let t := bit_and mask (bit_xor (unary a) (unary b)) in
  assign unary a := unary a bit_xor t ;;
  assign unary b := unary b bit_xor t ;;
  tt.

Definition conditional_select :=
  let mask := unary (choice ) in
  bit_xor a (bit_and mask (bit_xor a b)).

Definition conditional_assign :=
  let mask := unary (choice ) in
  assign unary self := unary self bit_xor bit_and mask (bit_xor (unary self) (unary other)) ;;
  tt.

Definition conditional_swap :=
  let mask := unary (choice ) in
  let t := bit_and mask (bit_xor (unary a) (unary b)) in
  assign unary a := unary a bit_xor t ;;
  assign unary b := unary b bit_xor t ;;
  tt.

Definition conditional_select :=
  Choice (conditional_select a.0 b.0 choice).

Error Trait.

Definition conditional_negate :=
  let self_neg := unary self in
  self self_neg choice ;;
  tt.

Error Struct.

Definition clone :=
  struct CtOption {value := $crate.clone.Clone.clone self.value;is_some := $crate.clone.Clone.clone self.is_some} .

Definition fmt :=
  debug_struct_field2_finish f "CtOption" "value" self.value "is_some" self.is_some.

Definition from :=
  if eq ((source ) ) 1 then
    Option.Some source.value
  else
    None.

Definition new :=
  struct CtOption {value := value;is_some := is_some} .

Definition expect :=
  match (self.is_some ,1) with (left_val,right_val) => if unary (eq (unary left_val) (unary right_val)) then
    let kind := $crate.panicking.AssertKind.Eq in
    $crate.panicking.assert_failed kind (unary left_val) (unary right_val) ($crate.option.Option.Some (new_v1 [""] [new_display msg])) ;;
    tt
  else
    tt end ;;
  self.value.

Definition unwrap :=
  match (self.is_some ,1) with (left_val,right_val) => if unary (eq (unary left_val) (unary right_val)) then
    let kind := $crate.panicking.AssertKind.Eq in
    $crate.panicking.assert_failed kind (unary left_val) (unary right_val) $crate.option.Option.None ;;
    tt
  else
    tt end ;;
  self.value.

Definition unwrap_or :=
  conditional_select def self.value self.is_some.

Definition unwrap_or_else :=
  conditional_select (f ) self.value self.is_some.

Definition is_some :=
  self.is_some.

Definition is_none :=
  unary self.is_some.

Definition map :=
  new (f (conditional_select (default ) self.value self.is_some)) self.is_some.

Definition and_then :=
  let tmp := f (conditional_select (default ) self.value self.is_some) in
  assign tmp.is_some := tmp.is_some bit_and self.is_some ;;
  tmp.

Definition or_else :=
  let is_none := self  in
  let f := f  in
  conditional_select self f is_none.

Definition conditional_select :=
  new (conditional_select a.value b.value choice) (conditional_select a.is_some b.is_some choice).

Definition ct_eq :=
  let a := self  in
  let b := rhs  in
  bit_and (bit_and (bit_and a b) (self.value rhs.value)) (bit_and (unary a) (unary b)).

Error Trait.

Definition ct_gt :=
  let gtb := bit_and self (unary other) in
  let ltb := bit_and (unary self) other in
  let pow := 1 in
  loop (if lt pow 8 then
    assign ltb := ltb bit_and shr ltb pow ;;
    assign pow := pow add pow ;;
    tt
  else
    Break ;;
    tt) from while ;;
  let bit := bit_and gtb (unary ltb) in
  let pow := 1 in
  loop (if lt pow 8 then
    assign bit := bit bit_and shr bit pow ;;
    assign pow := pow add pow ;;
    tt
  else
    Break ;;
    tt) from while ;;
  from (bit_and bit 1).

Definition ct_gt :=
  let gtb := bit_and self (unary other) in
  let ltb := bit_and (unary self) other in
  let pow := 1 in
  loop (if lt pow 16 then
    assign ltb := ltb bit_and shr ltb pow ;;
    assign pow := pow add pow ;;
    tt
  else
    Break ;;
    tt) from while ;;
  let bit := bit_and gtb (unary ltb) in
  let pow := 1 in
  loop (if lt pow 16 then
    assign bit := bit bit_and shr bit pow ;;
    assign pow := pow add pow ;;
    tt
  else
    Break ;;
    tt) from while ;;
  from (bit_and bit 1).

Definition ct_gt :=
  let gtb := bit_and self (unary other) in
  let ltb := bit_and (unary self) other in
  let pow := 1 in
  loop (if lt pow 32 then
    assign ltb := ltb bit_and shr ltb pow ;;
    assign pow := pow add pow ;;
    tt
  else
    Break ;;
    tt) from while ;;
  let bit := bit_and gtb (unary ltb) in
  let pow := 1 in
  loop (if lt pow 32 then
    assign bit := bit bit_and shr bit pow ;;
    assign pow := pow add pow ;;
    tt
  else
    Break ;;
    tt) from while ;;
  from (bit_and bit 1).

Definition ct_gt :=
  let gtb := bit_and self (unary other) in
  let ltb := bit_and (unary self) other in
  let pow := 1 in
  loop (if lt pow 64 then
    assign ltb := ltb bit_and shr ltb pow ;;
    assign pow := pow add pow ;;
    tt
  else
    Break ;;
    tt) from while ;;
  let bit := bit_and gtb (unary ltb) in
  let pow := 1 in
  loop (if lt pow 64 then
    assign bit := bit bit_and shr bit pow ;;
    assign pow := pow add pow ;;
    tt
  else
    Break ;;
    tt) from while ;;
  from (bit_and bit 1).

Error Trait.