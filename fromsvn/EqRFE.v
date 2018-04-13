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
  apply shiftinLast.
Defined.

Definition erMapNewPrevious : ∀ {n c : nat}, ∀ e : ER n c,
                              ∀ t : Fin.t n,
           (e ←▪) ↓ (FU t) = FU (e ↓ t).
Proof.
  intros n c e t.
  replace ((e ←▪) ↓ (FU t)) with
          (nth (shiftin (FL c) (map FU (erMapVector e))) (FU t)) 
           by trivial.
  rewrite (shiftinPrevious (FL c) (map FU (erMapVector e)) t).
  apply nthMapLemma.
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
           (e ← x) ↓ (FU t) = (e ↓ t).
Proof.
  intros n c e x t.
  replace ((e ← x) ↓ (FU t)) with
          (nth (shiftin x (erMapVector e)) (FU t)) 
          by trivial.
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

(* the class map of idRel is the identity *)

Equations idRelId {n : nat} (x : Fin.t n) : △ ↓ x = x :=
idRelId {n:=0}     x :=! x;
idRelId {n:=(S _)} x <= finFUOrFL x => {
                     | (inl (existT y eq (* x = FU y *))) :=
                       (* △ ↓ x *) (eq_trans
                         (f_equal _ eq)
                       (* △ ↓ (FU y) *) (eq_trans
                         (erMapNewPrevious △ y)
                       (* FU (△ ↓ y) *) (eq_trans
                         (f_equal FU (idRelId y))
                       (* FU y *)
                         (eq_sym eq))));
                     | (inr eq) (* x = FL _ *) := 
                       (* △ ↓ x *) (eq_trans
                         (f_equal _ eq)
                       (* △ ↓ (FL n') *) (eq_trans
                         (erMapNewLast △)
                       (* FL n' *)
                         (eq_sym eq)))}.

(* composition *)

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

(* erMap of "e1 • e2" is composition of erMaps *)

Ltac erRewrites0 := 
  try repeat  (rewrite erMapNewPrevious) ||
              (rewrite erMapNewLast)     ||
              (rewrite erMapPutPrevious) ||
              (rewrite erMapPutLast)     || trivial.

Obligation Tactic := program_simpl; erRewrites0.

Equations erMapCompose {n m l : nat} (e1 : ER n m)
      (e2 : ER m l) (x : Fin.t n) :
      (e1 • e2) ↓ x = e2 ↓ (e1 ↓ x) :=
erMapCompose {n:=0}     _ _ x :=! x;
erMapCompose {n:=(S _)} e1 e2 x <= finFUOrFL x => {
  erMapCompose {n:=(S _)} (ERNew e1')    (ERNew e2')    x (inl (existT y eq)) 
                                   <= erMapCompose e1' e2' y => { | IH := _};
  erMapCompose {n:=(S _)} (ERNew e1')    (ERNew e2')    x (inr eq)            := _;
  erMapCompose {n:=(S _)} (ERNew e1')    (ERPut t2 e2') x (inl (existT y eq)) := _;
  erMapCompose {n:=(S _)} (ERNew e1')    (ERPut t2 e2') x (inr eq)            := _;
  erMapCompose {n:=(S _)} (ERPut t1 e1')  e2            x (inl (existT y eq)) := _;
  erMapCompose {n:=(S _)} (ERPut t1 e1')  e2            x (inr eq)            := _}.
Next Obligation.
  rewrite IH. trivial.
Defined.

Obligation Tactic := program_simpl.

Lemma erComposeAssociative {n m l k : nat}
      (e1 : ER n m) (e2 : ER m l) (e3 : ER l k) :
      (e1 • e2) • e3 = e1 • e2 • e3.
Proof.
  funelim (e1 • e2).
  - funelim (□ • e3). trivial.
  - funelim ((e • e0 ←▪) • e3).
    + repeat (rewrite composeER_equation_2).
      rewrite H1. trivial.
    + repeat (rewrite composeER_equation_3).
      rewrite H1. trivial.
  - repeat (rewrite composeER_equation_4).
    rewrite composeER_equation_3.
    rewrite H. trivial.
  - repeat (rewrite composeER_equation_4).
    rewrite H. rewrite erMapCompose. trivial.
Defined.

Definition erContains {n m l : nat} (f: ER n m) (e: ER n l) : Type :=
           { d : ER m l | f • d = e }.

Notation "f '⊑' e" := (erContains f e) (at level 50).
                      (* \sqsubseteq *)

(* needed ?
Lemma erContainsUnique {n m l : nat} (f: ER n m) (e: ER n l)
         (d1 d2 : f ⊑ e) : d1 = d2.
Proof.
  destruct d1 as [d1 eq1].
  destruct d2 as [d2 eq2].
...
*)

Definition erContainsReflexive {n m : nat} (e : ER n m) : e ⊑ e :=
           (exist _ △  (idRelRight1 e)).

Definition erContainsTransitive {n c1 c2 c3 : nat} 
           (e1 : ER n c1) (e2 : ER n c2) (e3 : ER n c3) :
           (e1 ⊑ e2) → (e2 ⊑ e3) → (e1 ⊑ e3).
Proof.
  intros [d1 eq1] [d2 eq2].
  exists (d1 • d2).
  rewrite <- erComposeAssociative.
  rewrite eq1.
  exact eq2.
Defined.

(* to formulate and prove antisymmetry, we need EqR *)

Definition EqR (n : nat) : Type :=
      { c : nat & ER n c }.

Definition eqrContains {n : nat} (f e : EqR n) : Type :=
      (projT2 f) ⊑ (projT2 e).

Notation "e '⊆' f" := (eqrContains e f) (at level 50).

Definition eqrContainsReflexive {n : nat} (e : EqR n) : e ⊆ e :=
            erContainsReflexive (projT2 e).

Definition eqrContainsTransitive {n : nat} 
           (e1 e2 e3 : EqR n) :
           (e1 ⊆ e2) → (e2 ⊆ e3) → (e1 ⊆ e3).
Proof.
  apply erContainsTransitive.
Defined.

(* not needed...
Equations leDichoAlt (n m : nat) (nLEm : n ≤ m) (mLn : m < n) : False :=
leDichoAlt n ?(n) le_n y := nleSuccDiagL _ y;
leDichoAlt n _ (le_S nLEm) y <= leTrans _ _ _ y nLEm =>
             | SSmLEm  <= leTrans _ _ _ (le_S _ _ (le_n _)) SSmLEm => 
             | SmLEm := nleSuccDiagL _ SmLEm.

Equations leDicho2 (n m : nat) (nLEm : n ≤ m) : (n = m) + (n < m) :=
leDicho2 n m nLEm <= ltTricho n m =>
          | (inl (inl mEQn)) := inl (eq_sym mEQn);
          | (inl (inr mLTn)) := False_rect _ (leDichoAlt n m nLEm mLTn);
          | (inr nLTm)       := inr nLTm.
*)


Lemma eqrContainsAntiSymmetric {n : nat}
          (e1 e2 : EqR n) :
          (e1 ⊆ e2) → (e2 ⊆ e1) → e1 = e2.
Proof.
  destruct e1 as [c1 e1].
  destruct e2 as [c2 e2].
  unfold "⊆". simpl.
  intros [d1 eq1] [d2 eq2].
  pose (erCLeN d1) as C2LeC1.
  pose (erCLeN d2) as C1LeC2.
  pose (leAntiSymmetric _ _ (conj C1LeC2 C2LeC1)) as eq.
  destruct eq.
  pose (ernnIdRel d1) as d1Id.
  rewrite d1Id in eq1.
  rewrite (idRelRight1 e1) in eq1.
  rewrite eq1.
  trivial.
Defined.

Equations allRel {n : nat} : ER (S n) 1 :=
allRel {n:=O}     := □ ←▪;
allRel {n:=(S m)} := allRel ← F1.

Notation "▽" := allRel.
         (* \bigtriangledown *)

Definition idEqr {n : nat} : EqR n := existT _ n △.

Equations allEqr {n : nat} : EqR n := 
allEqr {n:=0}     := existT _ 0 □;
allEqr {n:=(S _)} := existT _ 1 ▽.

Notation "'Δ'" := idEqr.
         (* \Delta *)
Notation "'∇'" := allEqr.
         (* \nabla *)

Definition idEqrMin {n : nat} (e : EqR n) : Δ ⊆ e.
Proof.
  destruct e as [d e].
  unfold "⊆". simpl.
  exists e.
  apply idRelLeft1.
Defined.

(* any equivalence relation with exactly 1 class is ▽ *)
(*
Equations ern1AllRel {n : nat} (e : ER (S n) 1) : e ← F1 = ▽ :=
*)

Equations ern1AllRel {n : nat} (e : ER (S n) 1) : e = ▽ :=
ern1AllRel {n:=0}      (ERNew □)           := eq_refl;
ern1AllRel {n:=(S _)}  (ERNew (ERPut t _)) :=! t;
ern1AllRel {n:=(S _)}  (ERPut F1 e1)       := f_equal (ERPut F1) (ern1AllRel e1).

Definition allRelRight {n d : nat} (e : ER (S n) (S d)) : e • ▽ = ▽.
Proof.
  apply ern1AllRel.
Defined.

Equations allEqrMax {n : nat} (e : EqR n) : e ⊆ ∇ :=
allEqrMax {n:=0}     (existT 0 □)            := eqrContainsReflexive _;
allEqrMax {n:=(S _)} (existT 0 (ERPut t e1)) :=! t;
allEqrMax {n:=(S _)} (existT (S _) e1)       := _.
Next Obligation.
  unfold "⊆". simpl.
  exists ▽.
  apply allRelRight.
Defined.

(* subsets ... *)

Inductive Sub : nat → Type :=
  | SEmpty : Sub 0
  | SNew   : ∀ {n : nat}, Sub n → Sub (S n)
  | SOld   : ∀ {n : nat}, Sub n → Sub (S n).

Equations emptySub {n : nat} : Sub n :=
emptySub {n:=0}      := SEmpty;
emptySub {n:=(S n')} := SOld emptySub.

Equations subMeet {n : nat} (s1 s2 : Sub n) : Sub n :=
subMeet SEmpty     _        := SEmpty;
subMeet (SNew t1) (SNew t2) := SNew (subMeet t1 t2);
subMeet (SNew t1) (SOld t2) := SOld (subMeet t1 t2);
subMeet (SOld t1) (SNew t2) := SOld (subMeet t1 t2);
subMeet (SOld t1) (SOld t2) := SOld (subMeet t1 t2).

Equations subJoin {n : nat} (s1 s2 : Sub n) : Sub n :=
subJoin SEmpty     _        := SEmpty;
subJoin (SNew t1) (SNew t2) := SNew (subJoin t1 t2);
subJoin (SNew t1) (SOld t2) := SNew (subJoin t1 t2);
subJoin (SOld t1) (SNew t2) := SNew (subJoin t1 t2);
subJoin (SOld t1) (SOld t2) := SOld (subJoin t1 t2).

Equations singleSub {n : nat} (x : Fin.t n) : Sub n :=
singleSub {n:=0} x     :=! x;
singleSub {n:=(S _)} x <= finFUOrFL x => {
                       | (inl (existT x' _)) <= (singleSub x') => {
                          | s :=  SOld s };
                       | (inr _) := SNew emptySub  }.

(* a subset s defines an equivalence relation that
   connects the elements of s *)

(* we need a type that has an equivalence and maybe a
   distinguished equivalence class  *)

Definition EqRMaybeStar (n : nat) : Type :=
          { d : nat & (ER n d * option (Fin.t d))%type}.

Equations eqrFromSub' {n : nat} (s : Sub n) : EqRMaybeStar n :=
eqrFromSub' SEmpty := (existT _ 0 (□ , None));
(* this complains about non-exhaustive pattern matching ???
eqrFromSub' (SOld s) with (eqrFromSub' s) := {
                                | (existT _ d (pair _ _ e None))
                                := existT _ (S d) (e ←▪, None);
                                | existT _ d (pair _ _ e (Some t))
                                := existT _ (S d) (e ←▪ , Some (FU t))};
eqrFromSub' (SNew s) with (eqrFromSub' s) := {
                                | existT _ d (pair _ _ e None)
                                := existT (S d) (e ←▪ , Some (FL d));
                                | existT _ d (pair _ _ e  (Some t))
                                := existT _ d (e ← t , Some t)}.
so we have to do it with holes: *)
eqrFromSub' (SOld s) with (eqrFromSub' s) := {
                        |IH := _};
eqrFromSub' (SNew s) with (eqrFromSub' s) := {
                        |IH := _}.
Next Obligation.
  destruct IH as [d [e [t|]]]; exists (S d).
  - exact (e ←▪ , Some (FU t)).
  - exact (e ←▪ , None).
Defined.
Next Obligation.
  destruct IH as [d [e [t|]]].
  - exists d. exact (e ← t , Some t).
  - exists (S d). exact (e ←▪ , Some (FL d)).
Defined.
