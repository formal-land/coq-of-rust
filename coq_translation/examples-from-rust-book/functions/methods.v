Record Point : Set := {
  x : f64;
  y : f64;
}.

(* Impl [Point] *)
Module Point.
  Definition origin (_ : unit) : Point :=
    { Point.y := 0.0; Point.x := 1.0; } .
  
  Definition new (x : f64) (y : f64) : Point :=
    { Point.x := x; Point.y := y; } .
End Point.
(* End impl [Point] *)

Record Rectangle : Set := {
  p1 : Point;
  p2 : Point;
}.

(* Impl [Rectangle] *)
Module Rectangle.
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
End Rectangle.
(* End impl [Rectangle] *)

Definition Pair : Set :=
  Box * Box.

(* Impl [Pair] *)
Module Pair.
  Definition destroy (self : Self) :=
    let Pair (first, second) := self in
    _crate.io._print
      (_crate::fmt::Arguments.new_v1
        ["Destroying Pair(";", ";")\n"]
        [_crate::fmt::ArgumentV1.new_display
          first;_crate::fmt::ArgumentV1.new_display second]) ;;
    tt ;;
    tt.
End Pair.
(* End impl [Pair] *)

Definition main (_ : unit) :=
  let rectangle := {
    Rectangle.p1 := Point.origin tt;
    Rectangle.p2 := Point.new 3.0 4.0;
    }
     in
  _crate.io._print
    (_crate::fmt::Arguments.new_v1
      ["Rectangle perimeter: ";"\n"]
      [_crate::fmt::ArgumentV1.new_display (perimeter rectangle)]) ;;
  tt ;;
  _crate.io._print
    (_crate::fmt::Arguments.new_v1
      ["Rectangle area: ";"\n"]
      [_crate::fmt::ArgumentV1.new_display (area rectangle)]) ;;
  tt ;;
  let square := {
    Rectangle.p1 := Point.origin tt;
    Rectangle.p2 := Point.new 1.0 1.0;
    }
     in
  translate square 1.0 1.0 ;;
  let pair := Pair (Box.new 1) (Box.new 2) in
  destroy pair ;;
  tt.