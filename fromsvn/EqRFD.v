Require Import Utf8.
Require Import NatMisc.
Require Import Fin.
Require Import Decidable.
Require Import Vector.
Import VectorNotations.

(* How to build the type of all equivalence relations on the 
   (standard) n-element set {0,1,...,n-1} ? Just "describe" the 
   process of putting elements into their classes one by one: 

    - start with an empty list of classes
    - assuming {0,1,...,i-1} have been put into classes
      already, either
      + the element i is not related to any of the lower 
        elements, thus forming a new class, or
      + i belongs to one of the existing classes.

   This translates into an inductive definition of a type family 
   indexed by n and the number of classes:

   Inductive EqRF : nat -> nat -> Type :=
      | EqRFNone  : EqRF O O
      | EqRFNew   : forall {n c : nat},
                    EqRF n c ->
                    EqRF (S n) (S c)
      | EqRFPut   : forall {n c : nat},
                    Fin.t c ->  EqRF n c ->
                    EqRF (S n) c.

   It is a kind of heterogeneous list type. Nice, we would certainly
   like to concat such "lists", split them into sublists at a given
   index a.s.o. But ... what should be the type of, e.g. concat ?
      concat : {n0 c0 n1 c1 : nat} -> 
               EqRF n0 c0 -> EqRF n1 c1 -> EqRF (n0 + n1)  ???

   A slight generalization seems appropriate: Let's drop the 
   assumption that the process of "putting elements into their 
   classes" starts with an empty list of classes, i.e. the single 
   trivial equivalence on the empty set. Let's instead describe "how, 
   given an equivalence relation on n elements with c classes, we can
   extend it to an equivalence relation of m elements with d classes".
   We have to write more indizes, but gain some flexibility.

   The added "D" in the type name stands for "difference" or "delta".
*)

Inductive EqRFD : nat → nat → nat → nat → Type :=
  | EqRFDEmpty : ∀ {n c : nat}, EqRFD n c n c
  | EqRFDNew   : ∀ {n c m d : nat},
                 EqRFD n c m d → EqRFD n c (S m) (S d)
  | EqRFDPut   : ∀ {n c m d : nat},
                 Fin.t d → EqRFD n c m d →
                 EqRFD n c (S m) d.

(* the family of equivalence relations itself can be defined by 
   specialising *)

Definition EqRF (n c : nat) : Type := EqRFD 0 0 n c.

(* Notations *)

Notation "□"         := EqRFDEmpty.
Notation "eqr '←▪'"  := (EqRFDNew eqr) (at level 69, left associativity).
Notation "eqr '←' x" := (EqRFDPut x eqr) (at level 68, 
                                          left associativity).
Notation F2 := (FS F1). Notation F3 := (FS F2). 
Notation F4 := (FS F3). Notation F5 := (FS F4).
Notation F6 := (FS F5). Notation F7 := (FS F6).
Notation F8 := (FS F7). Notation F9 := (FS F8).

(* whenever EqRFD n c m d is inhabited, we have 
    n ≤ m, c ≤ d and d - c ≤ m - n *)

Lemma eqRFDleEl {n c m d : nat} : EqRFD n c m d → n ≤ m.
Proof.
  apply (EqRFD_ind
         (λ n c m d, λ e, n ≤ m)).
  - intros n' _. exact (le_n n').
  - intros n' _ m' _ _ n'Lem'. exact (le_S _ _ n'Lem').
  - intros n' _ m' _ _ _ n'Lem'. exact (le_S _ _ n'Lem').
Defined.

Lemma eqRFDleCl {n c m d : nat} : EqRFD n c m d → c ≤ d.
Proof.
  apply (EqRFD_ind
         (λ n c m d : nat, λ e : EqRFD n c m d, c ≤ d)).
  - intros _ c'. exact (le_n c').
  - intros _ c' _ d' _ c'Led'. exact (le_S _ _ c'Led').
  - intros _ c' _ d' _ _ c'Led'. exact (c'Led').
Defined.

Lemma eqRFDleDiff {n c m d : nat} : EqRFD n c m d → d - c ≤ m - n.
Proof.
  apply (EqRFD_ind
         (λ n c m d : nat, λ e : EqRFD n c m d, d - c ≤ m - n)).
  - intros n' c'. rewrite (subDiag c'). rewrite (subDiag n').
    exact (le_n 0).
  - intros n' c' m' d' e' le.
    rewrite (subSuccL c' d' (eqRFDleCl e')).
    rewrite (subSuccL n' m' (eqRFDleEl e')).
    apply (leNS).
    exact le.
  - intros n' c' m' d' idx e' le.
    rewrite (subSuccL n' m' (eqRFDleEl e')).
    apply (leTrans (d' - c') (m' - n') (S (m' - n')) le).
    exact (le_S _ _ (le_n (m' - n'))).
Defined.

(* in particular, if EqRF n c is inhabited, then c ≤ n *)

Definition eqRFle {n c : nat} : EqRF n c → c ≤ n.
Proof.
  intro eqR.
  pose (eqRFDleDiff eqR).
  rewrite (sub0R) in l.
  rewrite (sub0R) in l.
  exact l.
Defined.

(* we build the vector of length m - n, having at the ith position
   the class of the (n + i)th element of (Fin m) w.r.t. the given
   equivalence extension *)

Definition classMapVector {n c m d : nat} 
            (e : EqRFD n c m d) : Vector.t (Fin.t d) (m - n).
Proof.
  generalize dependent e.
  apply (EqRFD_rect
         (λ n' c' m' d', λ e', Vector.t (Fin.t d') (m' - n'))).
  - (* EqRFDEmpty *)
    intros n' c'. rewrite (subDiag n').
    exact (nil (Fin.t c')).
  - (* EqRFNew *)
    intros n' c' m' d' e v.
    rewrite (subSuccL _ _ (eqRFDleEl e)).
    exact (shiftin (of_nat_lt (le_n (S d'))) (map (L_R 1) v)).
  - (* EqRFPut *)
    intros n' c' m' d' i e v.
    rewrite (subSuccL _ _ (eqRFDleEl e)).
    exact (shiftin i v).
Defined.

(* here is the analogue to concat *)

Definition graftEqRFD {n0 c0 n1 c1 n2 c2 : nat}
            (d : EqRFD n1 c1 n2 c2) :
            (EqRFD n0 c0 n1 c1) → (EqRFD n0 c0 n2 c2).
Proof.
  generalize d.
  apply (EqRFD_rect (λ n1 c1 n2 c2, λ d, 
           EqRFD n0 c0 n1 c1 → EqRFD n0 c0 n2 c2)).
  - (* case EqRFDEmpty *)
    intros n3 c3 e. exact e.
  - (* case EqRFDNew *)
    intros n3 c3 n4 c4 _ IH e. exact ((IH e) ←▪).
  - (* case EqRFDPut *)
    intros n3 c3 n4 c4 idx _ IH e. exact ((IH e) ← idx).
Defined.

Notation "e '⇐' d" := (graftEqRFD d e)
                      (at level 71, left associativity).
                      (* \Leftarrow *)

(* concrete examples *)
(*
Definition test1 : EqRF 5 2 := □ ←▪ ← F1 ←▪ ← F2 ← F1.
Definition test2 : EqRFD 5 2 7 3 := □ ←▪ ← F2.
Definition test3 : EqRF 7 3 := test1 ⇐ test2.
Definition test4 : EqRF 7 3 := □ ←▪ ← F1 ←▪ ← F2 ← F1 ⇐ □ ←▪ ← F2.

(* these do compute to values *)
Eval compute in (test3).
Eval compute in (classMapVector test3).
Eval compute in (test1 ⇐ test2).
Eval compute in (classMapVector (test1 ⇐ test2)).
Eval compute in (classMapVector test4).

(* this one doesn't, since its type is not fixed *)
Eval compute in (classMapVector (□ ←▪ ← F1 ←▪ ← F2 ← F1 ⇐ □ ←▪ ← F2)).
*)

(* the identity relation *)

Fixpoint idEqRF (n : nat) : EqRF n n :=
  match n with
  | 0   => □
  | S n => (idEqRF n) ←▪
  end.

Fixpoint idEqRFD {n c : nat} (m : nat) : EqRFD n c (m + n) (m + c) :=
  match m with
  | 0   => □
  | S n => (idEqRFD n) ←▪
  end.

(* @gap n c m computes the equivalence extension 
   □ ←▪ ←▪ ... ←▪ ← t
   with m '←▪' and t equal to the class of the first '←▪', which
   is (S c) (embedded appropriately into a Fin.t ..)
*)
Definition gap {n c : nat} (m : nat) : EqRFD n c (S (S m) + n) (S m + c).
Proof.
  assert (c < S m + c) as pf.
  { rewrite (addSuccL m c).
    rewrite <- (addSuccR m c).
    exact (lePlusL m (S c)). }
  pose (of_nat_lt pf) as idx.
  exact ((@idEqRFD n c (S m)) ← idx).
Defined.

Eval compute in (idEqRF 1).
Eval compute in (idEqRF 3 ⇐ gap 0).
Eval compute in (idEqRF 1 ⇐ gap 2 ⇐ idEqRFD 3).

(* TODOs 
  - split

  - pairRel

  - compose
      type? in the special situation 
      EqRF m d -> EqRF d d' -> EqRF m d'

      EqRFD n c m d -> EqRF c c' d d' -> EqRF n c' m d'

      EqRFD n c m d inhabited -> 
                  n ≤ m , c ≤ d, c ≤ n , d ≤ m


*)



