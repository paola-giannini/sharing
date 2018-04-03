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

(* How to build the type of all equivalence relations on the 
   (standard) n-element set {0,1,...,n-1} ? Just "describe" the 
   process of putting elements into their classes one by one: 

    - start with an empty list of classes
    - assuming {0,1,...,i-1} have been put into classes
      already, either
      - the element i is not related to any of the lower 
        elements, thus forming a new class, or
      - i belongs to one of the existing classes.

   This translates into an inductive definition of a type family 
   indexed by n and the number of classes: 
*)

Inductive ER : nat -> nat -> Type :=
  | EREmpty : ER O O
  | ERNew   : ∀ {n c : nat},           ER n c → ER (S n) (S c)
  | ERPut   : ∀ {n c : nat}, Fin.t c → ER n c → ER (S n)  c.

Notation "□"       := EREmpty.                 (* \square *)
Notation "e '←▪'"  := (ERNew e) (at level 70). (* \leftarrow \blacksquare *)
Notation "e '←' x" := (ERPut x e) (at level 69, left associativity).
                                               (* \leftarrow *)

Notation F2 := (FS F1).  Notation F3 := (FS F2).
Notation F4 := (FS F3).  Notation F5 := (FS F4).
Notation F6 := (FS F5).  Notation F7 := (FS F6).
Notation F8 := (FS F7).  Notation F9 := (FS F8).

(* any element of ER 0 0 is equal to □ *)

Equations er00Empty (e : ER 0 0) : e = □ :=
er00Empty □ := eq_refl.

(* erMapVector n
   Vector of length n, having at ith position the class of the
   ith element of Fin.t n w.r.t. the given equivalence.

   erMapVector e is thus the tabulation of the map sending an
   element to its equivalence class. *)

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
          (Vector.nth (shiftin (FL c) (map FU (erMapVector e))) (FU t)) 
           by trivial.
  rewrite (shiftinPrevious' (FL c) (map FU (erMapVector e)) t).
  apply nthMapLemma.
Defined.

Definition erMapPutLast : ∀ {n c : nat}, ∀ e : ER n c,
                          ∀ x : Fin.t c,
           (e ← x) ↓ (FL n) = x.
Proof.
  intros n c e x.
  apply shiftinLast'.
Defined.

Definition erMapPutPrevious : ∀ {n c : nat}, ∀ e : ER n c,
                              ∀ x : Fin.t c, ∀ t : Fin.t n,
           (e ← x) ↓ (FU t) = (e ↓ t).
Proof.
  intros n c e x t.
  replace ((e ← x) ↓ (FU t)) with
          (Vector.nth (shiftin x (erMapVector e)) (FU t)) 
          by trivial.
  apply (shiftinPrevious' x (erMapVector e) t).
Defined.

(* the identity relation *)

Equations idRel {n : nat} : ER n n :=
idRel {n:=O}     := □;
idRel {n:=(S m)} := idRel ←▪.

Notation "△" := idRel.
         (* \bigtriangleup *)

(* Note: an analogue of Lemma EqRF.idRelStructure
    is auto-generated here as idRel_equation_2  *)

(* test computation
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

(* would be nice, but doesn't quite work..
Equations idRelId {n : nat} (x : Fin.t n) : △ ↓ x = x :=
idRelId {n:=0} x :=! x;
idRelId {n:=(S _)} x <= finFUOrFL x => {
                      | (inleft (exist y eq (* x = FU y *))) :=
                        (* △ ↓ x *)
                        ...;
                      | (inright eq) := _ }.
*)

Lemma idRelId : ∀ {n : nat}, ∀ x : Fin.t n, △ ↓ x = x.
Proof.
  induction n.
  - inversion x.
  - intro x.
    rewrite idRel_equation_2.
    destruct (finFUOrFL x) as [[y eq]|eq]; rewrite eq.
    + rewrite erMapNewPrevious.
      rewrite IHn.
      trivial.
    + apply erMapNewLast.
Defined.

Equations composeER {n c d: nat}
                 (e1 : ER n c) (e2 : ER c d) : ER n d :=
composeER {n:=0}      EREmpty       EREmpty       := EREmpty;
composeER {n:=(S _)} (ERNew e1')   (ERNew e2')    := 
                                        (ERNew (composeER e1' e2'));
composeER {n:=(S _)} (ERNew e1')   (ERPut t2 e2') := 
                                        (ERPut t2 (composeER e1' e2'));
composeER {n:=(S _)} (ERPut t1 e1') e2            := 
                                        (ERPut (e2 ↓ t1) (composeER e1' e2)).

(* Lemmata erComposeNN, ~NP and ~P are autogenerated as 
   composeER_equation_2, ~_3, ~_4  *)

Notation  "e1 '•' e2" := (@composeER _ _ _ e1 e2) 
                         (at level 60, right associativity).
          (* \bullet *)

(* example computation
Eval compute in ((□ ←▪ ← F1 ←▪ ← F2 ←▪) • (□ ←▪ ←▪ ← F2)).
*)

Equations idRelLeft1 {n c : nat} (e : ER n c) : △ • e = e :=
idRelLeft1 {n:=0}      EREmpty     :=  eq_refl;
idRelLeft1 {n:=(S _)} (ERNew e')   := (f_equal ERNew (idRelLeft1 e'));
idRelLeft1 {n:=(S _)} (ERPut t e') := (f_equal (ERPut t) (idRelLeft1 e')).

Equations idRelRight1 {n c : nat} (e : ER n c) : e • △ = e :=
idRelRight1 {n:=0}      EREmpty     :=  eq_refl;
idRelRight1 {n:=(S _)} (ERNew e')   := (f_equal ERNew (idRelRight1 e'));
idRelRight1 {n:=(S _)} (ERPut t e') :=
             (* (e' ← t) • △ *) (eq_trans
                (composeER_equation_4 _ _ _ _ _ _)
             (* (e' • △) ← (△ ↓ t) *) (eq_trans
                (f_equal (λ t', (ERPut t' (e' • △))) (idRelId t (* △ ↓ t = t *)))
             (* (e' • △) ← t *)
                (f_equal (ERPut t) (idRelRight1 e' (* e' • △ = e' *)))
             (* (e' ← t) *) )).

