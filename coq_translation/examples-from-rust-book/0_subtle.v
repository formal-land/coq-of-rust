Definition Choice (u8).

Definition clone :=
  let _ := tt in
  unary self.

Definition fmt :=
  debug_tuple_field1_finish f "Choice" self.0.

Definition unwrap_u8 :=
  self.0.

Definition from :=
  if true then
    if unary (Binary (Binary source.0 0) (Binary source.0 1)) then
      $crate.panicking.panic "assertion failed: (source.0 == 0u8) | (source.0 == 1u8)"
    else
      tt ;;
    tt
  else
    tt ;;
  Binary source.0 0.

Error ImplItemKind::Type.

Definition bitand :=
  (Binary self.0 rhs.0) .

Definition bitand_assign :=
  assign unary self := Binary (unary self) rhs ;;
  tt.

Error ImplItemKind::Type.

Definition bitor :=
  (Binary self.0 rhs.0) .

Definition bitor_assign :=
  assign unary self := Binary (unary self) rhs ;;
  tt.

Error ImplItemKind::Type.

Definition bitxor :=
  (Binary self.0 rhs.0) .

Definition bitxor_assign :=
  assign unary self := Binary (unary self) rhs ;;
  tt.

Error ImplItemKind::Type.

Definition not :=
  (Binary 1 (unary self.0)) .

Definition black_box :=
  if true then
    if unary (Binary (Binary input 0) (Binary input 1)) then
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
  if Binary len (_rhs ) then
    Return (from 0) ;;
    tt
  else
    tt ;;
  let x := 1 in
  match into_iter ((self ) (_rhs )) with iter => loop match next iter with None [] => Break Some [0 : (ai,bi)] => assign x := x Binary (ai bi)  ;;
  tt end ;;
  tt from for end ;;
  x .

Definition ct_eq :=
  unary (Binary (unary self) (unary rhs)).

Definition ct_eq :=
  let x := Binary self other in
  let y := Binary (Binary x (x )) (sub 8 1) in
  (Binary y 1) .

Definition ct_eq :=
  (unary self) (unary other).

Definition ct_eq :=
  let x := Binary self other in
  let y := Binary (Binary x (x )) (sub 16 1) in
  (Binary y 1) .

Definition ct_eq :=
  (unary self) (unary other).

Definition ct_eq :=
  let x := Binary self other in
  let y := Binary (Binary x (x )) (sub 32 1) in
  (Binary y 1) .

Definition ct_eq :=
  (unary self) (unary other).

Definition ct_eq :=
  let x := Binary self other in
  let y := Binary (Binary x (x )) (sub 64 1) in
  (Binary y 1) .

Definition ct_eq :=
  (unary self) (unary other).

Definition ct_eq :=
  let x := Binary self other in
  let y := Binary (Binary x (x )) (sub (mul ({{root}}.core.mem.size_of ) 8) 1) in
  (Binary y 1) .

Definition ct_eq :=
  (unary self) (unary other).

Error Trait.

Definition conditional_select :=
  let mask := unary (choice ) in
  Binary a (Binary mask (Binary a b)).

Definition conditional_assign :=
  let mask := unary (choice ) in
  assign unary self := unary self Binary Binary mask (Binary (unary self) (unary other)) ;;
  tt.

Definition conditional_swap :=
  let mask := unary (choice ) in
  let t := Binary mask (Binary (unary a) (unary b)) in
  assign unary a := unary a Binary t ;;
  assign unary b := unary b Binary t ;;
  tt.

Definition conditional_select :=
  let mask := unary (choice ) in
  Binary a (Binary mask (Binary a b)).

Definition conditional_assign :=
  let mask := unary (choice ) in
  assign unary self := unary self Binary Binary mask (Binary (unary self) (unary other)) ;;
  tt.

Definition conditional_swap :=
  let mask := unary (choice ) in
  let t := Binary mask (Binary (unary a) (unary b)) in
  assign unary a := unary a Binary t ;;
  assign unary b := unary b Binary t ;;
  tt.

Definition conditional_select :=
  let mask := unary (choice ) in
  Binary a (Binary mask (Binary a b)).

Definition conditional_assign :=
  let mask := unary (choice ) in
  assign unary self := unary self Binary Binary mask (Binary (unary self) (unary other)) ;;
  tt.

Definition conditional_swap :=
  let mask := unary (choice ) in
  let t := Binary mask (Binary (unary a) (unary b)) in
  assign unary a := unary a Binary t ;;
  assign unary b := unary b Binary t ;;
  tt.

Definition conditional_select :=
  let mask := unary (choice ) in
  Binary a (Binary mask (Binary a b)).

Definition conditional_assign :=
  let mask := unary (choice ) in
  assign unary self := unary self Binary Binary mask (Binary (unary self) (unary other)) ;;
  tt.

Definition conditional_swap :=
  let mask := unary (choice ) in
  let t := Binary mask (Binary (unary a) (unary b)) in
  assign unary a := unary a Binary t ;;
  assign unary b := unary b Binary t ;;
  tt.

Definition conditional_select :=
  let mask := unary (choice ) in
  Binary a (Binary mask (Binary a b)).

Definition conditional_assign :=
  let mask := unary (choice ) in
  assign unary self := unary self Binary Binary mask (Binary (unary self) (unary other)) ;;
  tt.

Definition conditional_swap :=
  let mask := unary (choice ) in
  let t := Binary mask (Binary (unary a) (unary b)) in
  assign unary a := unary a Binary t ;;
  assign unary b := unary b Binary t ;;
  tt.

Definition conditional_select :=
  let mask := unary (choice ) in
  Binary a (Binary mask (Binary a b)).

Definition conditional_assign :=
  let mask := unary (choice ) in
  assign unary self := unary self Binary Binary mask (Binary (unary self) (unary other)) ;;
  tt.

Definition conditional_swap :=
  let mask := unary (choice ) in
  let t := Binary mask (Binary (unary a) (unary b)) in
  assign unary a := unary a Binary t ;;
  assign unary b := unary b Binary t ;;
  tt.

Definition conditional_select :=
  let mask := unary (choice ) in
  Binary a (Binary mask (Binary a b)).

Definition conditional_assign :=
  let mask := unary (choice ) in
  assign unary self := unary self Binary Binary mask (Binary (unary self) (unary other)) ;;
  tt.

Definition conditional_swap :=
  let mask := unary (choice ) in
  let t := Binary mask (Binary (unary a) (unary b)) in
  assign unary a := unary a Binary t ;;
  assign unary b := unary b Binary t ;;
  tt.

Definition conditional_select :=
  let mask := unary (choice ) in
  Binary a (Binary mask (Binary a b)).

Definition conditional_assign :=
  let mask := unary (choice ) in
  assign unary self := unary self Binary Binary mask (Binary (unary self) (unary other)) ;;
  tt.

Definition conditional_swap :=
  let mask := unary (choice ) in
  let t := Binary mask (Binary (unary a) (unary b)) in
  assign unary a := unary a Binary t ;;
  assign unary b := unary b Binary t ;;
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
  if Binary ((source ) ) 1 then
    Option.Some source.value
  else
    None.

Definition new :=
  struct CtOption {value := value;is_some := is_some} .

Definition expect :=
  match (self.is_some ,1) with (left_val,right_val) => if unary (Binary (unary left_val) (unary right_val)) then
    let kind := $crate.panicking.AssertKind.Eq in
    $crate.panicking.assert_failed kind (unary left_val) (unary right_val) ($crate.option.Option.Some (new_v1 [""] [new_display msg])) ;;
    tt
  else
    tt end ;;
  self.value.

Definition unwrap :=
  match (self.is_some ,1) with (left_val,right_val) => if unary (Binary (unary left_val) (unary right_val)) then
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
  assign tmp.is_some := tmp.is_some Binary self.is_some ;;
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
  Binary (Binary (Binary a b) (self.value rhs.value)) (Binary (unary a) (unary b)).

Error Trait.

Definition ct_gt :=
  let gtb := Binary self (unary other) in
  let ltb := Binary (unary self) other in
  let pow := 1 in
  loop (if Binary pow 8 then
    assign ltb := ltb Binary Binary ltb pow ;;
    assign pow := pow add pow ;;
    tt
  else
    Break ;;
    tt) from while ;;
  let bit := Binary gtb (unary ltb) in
  let pow := 1 in
  loop (if Binary pow 8 then
    assign bit := bit Binary Binary bit pow ;;
    assign pow := pow add pow ;;
    tt
  else
    Break ;;
    tt) from while ;;
  from (Binary bit 1).

Definition ct_gt :=
  let gtb := Binary self (unary other) in
  let ltb := Binary (unary self) other in
  let pow := 1 in
  loop (if Binary pow 16 then
    assign ltb := ltb Binary Binary ltb pow ;;
    assign pow := pow add pow ;;
    tt
  else
    Break ;;
    tt) from while ;;
  let bit := Binary gtb (unary ltb) in
  let pow := 1 in
  loop (if Binary pow 16 then
    assign bit := bit Binary Binary bit pow ;;
    assign pow := pow add pow ;;
    tt
  else
    Break ;;
    tt) from while ;;
  from (Binary bit 1).

Definition ct_gt :=
  let gtb := Binary self (unary other) in
  let ltb := Binary (unary self) other in
  let pow := 1 in
  loop (if Binary pow 32 then
    assign ltb := ltb Binary Binary ltb pow ;;
    assign pow := pow add pow ;;
    tt
  else
    Break ;;
    tt) from while ;;
  let bit := Binary gtb (unary ltb) in
  let pow := 1 in
  loop (if Binary pow 32 then
    assign bit := bit Binary Binary bit pow ;;
    assign pow := pow add pow ;;
    tt
  else
    Break ;;
    tt) from while ;;
  from (Binary bit 1).

Definition ct_gt :=
  let gtb := Binary self (unary other) in
  let ltb := Binary (unary self) other in
  let pow := 1 in
  loop (if Binary pow 64 then
    assign ltb := ltb Binary Binary ltb pow ;;
    assign pow := pow add pow ;;
    tt
  else
    Break ;;
    tt) from while ;;
  let bit := Binary gtb (unary ltb) in
  let pow := 1 in
  loop (if Binary pow 64 then
    assign bit := bit Binary Binary bit pow ;;
    assign pow := pow add pow ;;
    tt
  else
    Break ;;
    tt) from while ;;
  from (Binary bit 1).

Error Trait.