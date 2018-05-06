Require Import EqRFE.

(* for convenience *)

Notation F2 := (FS F1).  Notation F3 := (FS F2). Notation F4 := (FS F3).
Notation F5 := (FS F4).  Notation F6 := (FS F5). Notation F7 := (FS F6).
Notation F8 := (FS F7).  Notation F9 := (FS F8).

(* test computation
Eval compute in (erMap (@idRel 5)).
*)

(* test computations
Eval compute in (erMap (# <* << F1 <* << F2 << F1)).
(* representation of [[1,2,5],[3,4,9],[6,8],[7]] *)
Eval compute in
    (erMap (# <* << F1 <* << F2 << F1 <* <* << F3 << F2)).
(*  [[1],[2,4],[3,5,6]] *)
Eval compute in (erMap (# <* <* <* << F2 << F3 << F3)).
*)

(* example computation
Eval compute in ((# <* << F1 <* << F2 <* ) ** (# <* <* << F2)).
*)

