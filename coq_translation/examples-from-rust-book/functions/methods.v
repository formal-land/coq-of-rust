Error Struct.

(* Impl [Point] *)
  Definition origin : Point :=
    struct Point {x := 0.0;y := 0.0} .
  
  Definition new (x : f64) (y : f64) : Point :=
    struct Point {x := x;y := y} .
(* End impl [Point] *)

Error Struct.

(* Impl [Rectangle] *)
  Definition area (self : ref Self) : f64 :=
    let Point [x : x1,y : y1] := self.p1 in
    let Point [x : x2,y : y2] := self.p2 in
    abs (mul (sub x1 x2) (sub y1 y2)).
  
  Definition perimeter (self : ref Self) : f64 :=
    let Point [x : x1,y : y1] := self.p1 in
    let Point [x : x2,y : y2] := self.p2 in
    mul 2.0 (add (abs (sub x1 x2)) (abs (sub y1 y2))).
  
  Definition translate (self : ref Self) (x : f64) (y : f64) :=
    assign self.p1.x := add self.p1.x x ;;
    assign self.p2.x := add self.p2.x x ;;
    assign self.p1.y := add self.p1.y y ;;
    assign self.p2.y := add self.p2.y y ;;
    tt.
(* End impl [Rectangle] *)

Definition Pair : Set :=
  Box * Box.

(* Impl [Pair] *)
  Definition destroy (self : Self) :=
    let Pair (first, second) := self in
    _crate.io._print
      (new_v1
        ["Destroying Pair(";", ";")\n"]
        [new_display first;new_display second]) ;;
    tt ;;
    tt.
(* End impl [Pair] *)

Definition main :=
  let rectangle := struct Rectangle {p1 := origin tt;p2 := new 3.0 4.0}  in
  _crate.io._print
    (new_v1
      ["Rectangle perimeter: ";"\n"]
      [new_display (perimeter rectangle)]) ;;
  tt ;;
  _crate.io._print
    (new_v1 ["Rectangle area: ";"\n"] [new_display (area rectangle)]) ;;
  tt ;;
  let square := struct Rectangle {p1 := origin tt;p2 := new 1.0 1.0}  in
  translate square 1.0 1.0 ;;
  let pair := Pair (new 1) (new 2) in
  destroy pair ;;
  tt.