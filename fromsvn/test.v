Require Import Utf8.
Require Import Fin.
Require Import Vector.
Import VectorNotations.

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

Fixpoint finLast (n : nat) : Fin.t (S n) :=
  match n with
  | 0      => F1
  | (S n') => FS (finLast n')
  end.

Fixpoint erMapVector {n c : nat}
              (e : ER n c) : Vector.t (Fin.t c) n :=
  match e with
  | □            => @nil (Fin.t 0)
  | (@ERNew _ _ e')   => shiftin (finLast _) (map (L_R 1) (erMapVector e'))
  | (@ERPut _ _ t e') => shiftin t (erMapVector e')
  end.

Fixpoint er00Empty (e : ER 0 0) : e = □ :=
   match e with
   | □ => eq_refl
   end.

