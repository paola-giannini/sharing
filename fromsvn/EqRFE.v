Require Import Utf8.
Require Import Decidable.
Require Import Arith.
Require Import NatMisc.
Require Import Fin.
Require Import Vector.
Require Import FinVectorMisc.
Import VectorNotations.
From Equations Require Import Equations.
Set Equations Transparent.
Unset Equations WithK.

Inductive ER : nat -> nat -> Type :=
  | EREmpty : ER O O
  | ERNew   : ∀ {n c : nat},           ER n c → ER (S n) (S c)
  | ERPut   : ∀ {n c : nat}, Fin.t c → ER n c → ER (S n)  c.

Notation "□"       := (* \square *) EREmpty.
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
erMapVector (ERNew e')   := shiftin (FL _) (map FU (erMapVector e'));
erMapVector (ERPut t e') := shiftin t (erMapVector e').


Notation "e '↓' t" := (Vector.nth (erMapVector e) t) (at level 5).
          (* \downarrow *)

(* test computations 
Eval compute in (erMapVector (□ ←▪ ← F1 ←▪ ← F2 ← F1)).
(* representation of [[1,2,5],[3,4,9],[6,8],[7]] *)
Eval compute in 
    (erMapVector (□ ←▪ ← F1 ←▪ ← F2 ← F1 ←▪ ←▪ ← F3 ← F2)).
(*  [[1],[2,4],[3,5,6]] *)
Eval compute in (erMapVector (□ ←▪ ←▪ ←▪ ← F2 ← F3 ← F3)).
*)

(* one step computation rules for ↓

   do we need them? can we prove them more concisely using Equations? *)

Definition erMapNewLast : ∀ {n c : nat}, ∀ e : ER n c,
           (e ←▪) ↓ (FL n) = FL c.
Proof.
  intros n c e.
  apply shiftinLast'.
Defined.

Definition erMapNewPrevious : ∀ {n c : nat}, ∀ e : ER n c,
                              ∀ t : Fin.t n,
           (e ←▪) ↓ (FU t) = FU (e ↓ t).
Proof.
  intros n c e t.
  replace ((e ←▪) ↓ (FU t)) with
          (Vector.nth
            (shiftin (FL c) (map FU (erMapVector e)))
            (FU t)) by trivial.
  rewrite (shiftinPrevious' (FL c) (map FU (erMapVector e)) t).
  apply (nthMapLemma).
Defined.

Definition erMapPutLast : ∀ {n c : nat}, ∀ e : ER n c,
                          ∀ x : Fin.t c,
           (e ← x) ↓ (FL n) = x.
Proof.
  intros n c e x.
  apply shiftinLast.
Defined.

Definition erMapPutPrevious : ∀ {n c : nat}, ∀ e : ER n c,
                              ∀ x : Fin.t c, ∀ t : Fin.t n,
           (e ← x) ↓ (L_R 1 t) = (e ↓ t).
Proof.
  intros n c e x t.
  replace ((e ← x) ↓ (L_R 1 t)) with
          (Vector.nth
            (shiftin x (erMapVector e))
            (L_R 1 t)) by trivial.
  apply (shiftinPrevious x (erMapVector e) t).
Defined.

(* the identity relation *)

Equations idRel {n : nat} : ER n n :=
idRel {n:=O}     := □;
idRel {n:=(S m)} := idRel ←▪.

Notation "△" := idRel.
         (* \bigtriangleup *)

(* Note: an analogue of Lemma EqRF.idRelStructure
    is auto-generated here as idRel_equation_2  *)

(* test computations
Eval compute in (erMapVector (@idRel 5)).
*)

(* if ER n c is inhabited, n ≥ c *)
Equations erCLeN {n c : nat} (e : ER n c) : c ≤ n :=
erCLeN  □           := @le_n 0;
erCLeN (ERNew e')   := leNS (erCLeN e');
erCLeN (ERPut t e') := le_S _ _ (erCLeN e').

(* idRel n is the only element of ER n n *)

Equations ernnIdRel {n : nat} (e : ER n n) : e = △ :=
ernnIdRel {n:=0}      □           := eq_refl;
ernnIdRel {n:=(S _)} (ERNew e')   := f_equal ERNew (ernnIdRel e');
ernnIdRel {n:=(S _)} (ERPut t e') := False_rect _ (nleSuccDiagL _ (erCLeN e')).

(* here we get problems when proving the obligations
Equations idRelId {n : nat} (x : Fin.t n) : △ ↓ x = x :=
idRelId {n:=0}      x  :=! x;
idRelId {n:=(S _ )} x <= finLastOrPrevious x => {
                      | (inleft _) => _;
                      | (inright eq) => _ }.
Next Obligation.
  compute.
  admit.
Admitted.
Next Obligation.
  rewrite shiftinLast.
  trivial.
Defined.
*)



Lemma idRelId : ∀ {n : nat}, ∀ x : Fin.t n, △ ↓ x = x.
Proof.
  induction n.
  - inversion x.
  - intro x.
    rewrite idRel_equation_2.
    destruct (finLastOrPrevious x) as [[y eq]|eq]; rewrite eq.
    + rewrite erMapNewPrevious.
      rewrite IHn.
      trivial.
    + apply erMapNewLast.
Defined.


