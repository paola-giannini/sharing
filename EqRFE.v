Require Import Utf8.
Require Import Decidable.
Require Import Arith.
Require Import NatMisc.
Require Import Fin.
Require Import Vector.
Require Import FinVectorMisc.
Import VectorNotations.
From Equations Require Import Equations.

Inductive ER : nat -> nat -> Type :=
  | EREmpty : ER O O
  | ERNew   : ∀ {n c : nat},           ER n c → ER (S n) (S c)
  | ERPut   : ∀ {n c : nat}, Fin.t c → ER n c → ER (S n)  c.

Notation "□"         := (* \square *) EREmpty.
Notation "e '←▪'"  := (* \leftarrow \blacksquare *)
                        (ERNew e) (at level 70).
Notation "e '←' x" := (* \leftarrow *)
                        (ERPut x e) (at level 69, 
                                        left associativity).

Notation F2 := (FS F1).  Notation F3 := (FS F2).
Notation F4 := (FS F3).  Notation F5 := (FS F4).
Notation F6 := (FS F5).  Notation F7 := (FS F6).
Notation F8 := (FS F7).  Notation F9 := (FS F8).

Equations er00Empty (e : ER 0 0) : e = □ :=
er00Empty □ := eq_refl.

Equations erMapVector {n c : nat}
              (e : ER n c) : Vector.t (Fin.t c) n :=
erMapVector □            := nil;
erMapVector (ERNew e')   := shiftin (finLast _) (map (L_R 1) (erMapVector e'));
erMapVector (ERPut t e') := shiftin t (erMapVector e').

Global Transparent erMapVector.

(*
Eval compute in (erMapVector (□ ←▪ ← F1 ←▪ ← F2 ← F1)).
(* representation of [[1,2,5],[3,4,9],[6,8],[7]] *)
Eval compute in 
    (erMapVector (□ ←▪ ← F1 ←▪ ← F2 ← F1 ←▪ ←▪ ← F3 ← F2)).
(*  [[1],[2,4],[3,5,6]] *)
Eval compute in (erMapVector (□ ←▪ ←▪ ←▪ ← F2 ← F3 ← F3)).
*)

