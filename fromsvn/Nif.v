Require Import Utf8.
Require Import Arith.
Require Import Fin.
Require Import Vector.
Import VectorNotations.
From Equations Require Import Equations.
Set Equations Transparent.
Unset Equations WithK.

Inductive Nif : nat → Type :=
    | FL : ∀ {n : nat}, Nif (S n)
    | FU : ∀ {n : nat}, Nif n → Nif (S n).

Equations fromFin {n : nat} (x : Fin.t n) : Nif n :=
  fromFin {n:=0}     x      :=! x;
  fromFin {n:=(S _)} F1     := FL;
  fromFin {n:=(S _)} (FS y) := FU (fromFin y).

Equations toFin {n : nat} (x : Nif n) : Fin.t n :=
  toFin {n:=0}     x        :=! x;
  toFin {n:=(S _)} FL       := F1;
  toFin {n:=(S _)} (FU y)   := FS (toFin y).

Equations toFromFin {n : nat} (x : Fin.t n) :
          toFin (fromFin x) = x :=
  toFromFin {n:=0}      x     :=! x;
  toFromFin {n:=(S _)}  F1    := eq_refl;
  toFromFin {n:=(S _)} (FS y) := (f_equal FS (toFromFin y)).

Equations fromToFin {n : nat} (x : Nif n) :
          fromFin (toFin x) = x :=
  fromToFin {n:=0}      x     :=! x;
  fromToFin {n:=(S _)}  FL    := eq_refl;
  fromToFin {n:=(S _)} (FU y) := (f_equal FU (fromToFin y)).

Print Grammar constr.

