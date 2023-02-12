Error Struct.

Definition fmt
  (self : ref Self)
  (f : ref $crate.fmt.Formatter)
  : $crate.fmt.Result :=
  debug_struct_field2_finish f "Person" "name" self.name "age" self.age.

Error Struct.

Definition Pair : Set :=
  i32 * f32.

Error Struct.

Error Struct.

Definition main :=
  let name := from "Peter" in
  let age := 27 in
  let peter := struct Person {name := name;age := age}  in
  $crate.io._print (new_v1 ["";"\n"] [new_debug peter]) ;;
  tt ;;
  let point := struct Point {x := 10.3;y := 0.4}  in
  $crate.io._print (new_v1 ["point coordinates: (";", ";")\n"] [new_display point.x;new_display point.y]) ;;
  tt ;;
  let bottom_right := struct Point {x := 5.2} with point in
  $crate.io._print (new_v1 ["second point: (";", ";")\n"] [new_display bottom_right.x;new_display bottom_right.y]) ;;
  tt ;;
  let Point [x : left_edge,y : top_edge] := point in
  let _rectangle := struct Rectangle {top_left := struct Point {x := left_edge;y := top_edge} ;bottom_right := bottom_right}  in
  let _unit := Unit in
  let pair := Pair 1 0.1 in
  $crate.io._print (new_v1 ["pair contains ";" and ";"\n"] [new_debug pair.0;new_debug pair.1]) ;;
  tt ;;
  let Pair (integer, decimal) := pair in
  $crate.io._print (new_v1 ["pair contains ";" and ";"\n"] [new_debug integer;new_debug decimal]) ;;
  tt ;;
  tt.