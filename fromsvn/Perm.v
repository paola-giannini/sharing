Require Import Decidable.
Require Import Arith.
Require Import Fin.
Require Import Vector.
Require Import FinVectorMisc.
Require Import NatMisc.
Import VectorNotations.
From Equations Require Import Equations.
Unset Equations WithK.
Set Equations Transparent.

Notation F2 := (FS F1).  Notation F3 := (FS F2). Notation F4 := (FS F3).
Notation F5 := (FS F4).  Notation F6 := (FS F5). Notation F7 := (FS F6).
Notation F8 := (FS F7).  Notation F9 := (FS F8).

(** Permutations on an n-element set **)

Inductive Perm : nat -> Type :=
  | PEmpty : Perm 0
  | PPut   : forall {n : nat}, Fin.t (S n) -> Perm n -> Perm (S n).

(* the identity permutation *)

Equations idPerm {n : nat} : Perm n :=
idPerm {n:=0}     := PEmpty;
idPerm {n:=(S _)} := PPut (FL _) idPerm.

Equations vectAllFin (n : nat) : Vector.t (Fin.t n) n :=
vectAllFin 0       := [];
vectAllFin (S n')  := F1 :: map FS (vectAllFin n').

Equations gapAt {n : nat} (x : Fin.t (S n)) (y : Fin.t n) : Fin.t (S n) :=
gapAt {n:=0}     _  y :=! y;
gapAt {n:=(S _)} x y with leFDecidable x y := {
                          | (left _)  := FS y;
                          | (right _) := FU y}.

Transparent gapAt. (* needed to make it compute! global setting not enough ...? *)

(* test computation
Eval compute in (map (@gapAt 3 F3) [F1;F2;F3]).
*)

Equations permStep {n : nat} (x : Fin.t (S n)) (y : Fin.t (S n)) : Fin.t (S n) :=
permStep x y with finFUOrFL y := {
                  | (inl (existT z _)) := gapAt x z;
                  | (inr _)            := x}.

(* test computation
Eval compute in (map (@permStep 4 F2) [F1;F2;F3;F4]).
*)

Equations permMap {n : nat} (p : Perm n) : Vector.t (Fin.t n) n :=
permMap PEmpty     := [];
permMap (PPut x q) := map (permStep x) 
                          (shiftin (FL _) (map FU (permMap q))).

(* test computation
Eval compute in (permMap (PPut F3 (PPut F1 (PPut F1 PEmpty)))).
*)