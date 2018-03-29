Require Import Utf8.
Require Import Decidable.
Require Import Arith.
Require Import NatMisc.
Require Import Fin.
Require Import Vector.
Require Import FinVectorMisc.
Import VectorNotations.

(*
   How to build the type of all equivalence relations on the 
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

Notation "□"       := EREmpty.
          (* \square *)
Notation "e '←▪'"  := (ERNew e) (at level 70).
          (* \leftarrow \blacksquare *)
Notation "e '←' x" := (ERPut x e) (at level 69, left associativity).
          (* \leftarrow *)

Notation F2 := (FS F1).  Notation F3 := (FS F2).
Notation F4 := (FS F3).  Notation F5 := (FS F4).
Notation F6 := (FS F5).  Notation F7 := (FS F6).
Notation F8 := (FS F7).  Notation F9 := (FS F8).

(* if ER n c is inhabited, then n ≥ c *)

Lemma erCLeN : ∀ {n c : nat}, ER n c → c ≤ n.
Proof.
  induction 1.
  - trivial.
  - apply leNS; trivial.
  - apply le_S; trivial.
Defined.

(* if ER n c is inhabited and n ≠ 0, then c ≠ 0 *)

Lemma erCNot0 : ∀ {n c : nat}, ER n c → n ≠ 0 → c ≠ 0.
Proof.
  induction 1.
  - trivial.
  - intros. apply neqSucc0.
  - intros _ cEq0.
    rewrite cEq0 in t.
    inversion t.
Defined.

(* ER (S n) 0 and ER 0 (S c) are uninhabited, i.e. given an
   an element of such a type we can prove anything *)

Lemma erS0Absurd : ∀ {n : nat} {A : Type}, 
             ER (S n) 0 -> A.
Proof.
  intros n A e.
  apply False_rect.
  exact ((erCNot0 e (neqSucc0 n)) eq_refl).
Defined.

Lemma er0SAbsurd : ∀ {c : nat} {A : Type}, 
             ER 0 (S c) -> A.
Proof.
  intros c A e.
  apply False_rect.
  apply (neqSucc0 c).
  exact (le0eq0 _ (erCLeN e)).
Defined.

(* to prove something for all elements of ER 0 0, it
   is enough to prove it for □ *)

Lemma er00_rect : ∀ P : ER 0 0 → Type, (P □) →
                  ∀ (e : ER 0 0), P e.
Proof.
  intros P caseEmpty.
  (* extend P to a type family on all equivalences so
     ER_rect applies *)
  pose (λ n, λ c,
    match (n, c) as p return ER (fst p) (snd p) → Type with
    | (0, 0)  => λ e, P e
    | _       => λ e, True
    end ) as P'.
  apply (ER_rect P'); intros; compute; trivial.
Defined.

(* in particular, any element of ER 0 0 is equal to □ *)

Lemma er00Empty (e : ER 0 0) : e = □.
Proof.
  apply (er00_rect (λ e, e = □)).
  trivial.
Defined.

(* elements of ER (S n) (S c) are built as (e' ←▪) or (e' ← t).
   In most situations, destructing (erCase e) works better than
   pattern matching on e *)

Definition erCase {n c : nat} (e : ER (S n) (S c)) :
                sum { e' | e = (e' ←▪) } 
                    { p  | e = (fst p) ← (snd p) }.
Proof.
  refine ( 
    match e in ER (S n) (S c)
            return sum { e' | e = (e' ←▪) } 
                       { p  | e = (fst p) ← (snd p) } with
         | e' ←▪  => inl (exist _ e' eq_refl)
         | e' ← t => _
         end ).
  - destruct n1.
    + inversion t.
    + right. exists (e', t). trivial.
Defined.


(* erMapVector
   Vector of length n, having at ith position the class of the
   ith element of Fin.t n w.r.t. the given equivalence.

   erMapVector e is thus the tabulation of the map sending an
   element to its equivalence class.
*)

Definition erMapVector : ∀ {n c : nat},
              ER n c → Vector.t (Fin.t c) n.
Proof.
  induction 1.
  - (* case □ *)
    exact nil.
  - (* case _ ←▪ *)
    exact (shiftin (finLast c) (map (L_R 1) IHER)).
  - (* case _ ← t *)
    exact (shiftin t IHER).
Defined.

Notation "e '↓' t" := (Vector.nth (erMapVector e) t) (at level 5).
          (* \downarrow *)

(* example computations ...
Eval compute in (erMapVector (□ ←▪ ← F1 ←▪ ← F2 ← F1)).
(* representation of [[1,2,5],[3,4,9],[6,8],[7]] *)
Eval compute in 
    (erMapVector (□ ←▪ ← F1 ←▪ ← F2 ← F1 ←▪ ←▪ ← F3 ← F2)).
(*  [[1],[2,4],[3,5,6]] *)
Eval compute in (erMapVector (□ ←▪ ←▪ ←▪ ← F2 ← F3 ← F3)).
*)

(* one step computation rules for ↓ *)

Definition erMapNewLast : ∀ {n c : nat}, ∀ e : ER n c,
           (e ←▪) ↓ (finLast n) = finLast c.
Proof.
  intros n c e.
  apply shiftinLast.
Defined.

Definition erMapNewPrevious : ∀ {n c : nat}, ∀ e : ER n c,
                              ∀ t : Fin.t n,
           (e ←▪) ↓ (L_R 1 t) = L_R 1 (e ↓ t).
Proof.
  intros n c e t.
  replace ((e ←▪) ↓ (L_R 1 t)) with
          (Vector.nth
            (shiftin (finLast c) (map (L_R 1) (erMapVector e)))
            (L_R 1 t)) by trivial.
  rewrite (shiftinPrevious (finLast c)
                           (map (L_R 1)(erMapVector e)) t).
  apply (nthMapLemma).
Defined.

Definition erMapPutLast : ∀ {n c : nat}, ∀ e : ER n c,
                          ∀ x : Fin.t c,
           (e ← x) ↓ (finLast n) = x.
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

Definition idRel {n : nat} : ER n n.
Proof.
  induction n.
  - exact □.
  - exact (IHn ←▪).
Defined.

Notation "△" := idRel.
         (* \bigtriangleup *)

(* idRel n is the only element of ER n n *)

Lemma ernnIdRel : ∀ {n : nat}, ∀ e : ER n n, e = △.
Proof.
  induction n.
  - intro e. compute. exact (er00Empty e).
  - intro e.
    destruct (erCase e) as [[e' eq]|[[eimp _] _]].
    + rewrite (IHn e') in eq.
      rewrite eq. trivial.
    + apply False_rec.
      apply (nleSuccDiagL n).
      apply erCLeN.
      exact eimp.
Defined.

(* △ = (△ ←▪) *)

Lemma idRelStructure : ∀ {n : nat}, @idRel (S n) = (△ ←▪).
Proof.
  trivial.
Defined.

(* erMap of idRel is the identity *)

Lemma idRelId : ∀ {n : nat}, ∀ x : Fin.t n, △ ↓ x = x.
Proof.
  induction n.
  - inversion x.
  - intro x.
    rewrite idRelStructure.
    destruct (finLastOrPrevious x) as [[y eq]|eq]; rewrite eq.
    + rewrite erMapNewPrevious.
      rewrite IHn.
      trivial.
    + apply erMapNewLast.
Defined.

(* compose equivalences *)

Definition composeER {n : nat} : ∀ {c d : nat},
                   ER n c → ER c d → ER n d.
Proof.
  induction n.
  - intros c d e1 e2.
    rewrite (le0eq0 c (erCLeN e1)) in e2.
    rewrite (le0eq0 d (erCLeN e2)).
    exact □.
  - destruct c.
    + intros d e1. apply (erS0Absurd e1).
    + destruct d.
      * intro. apply erS0Absurd.
      * intros e1 e2.
        destruct (erCase e1) as [[e1' _]|[[e1' t1] _]].
        { destruct (erCase e2) as [[e2' _]|[[e2' t2] _]].
          - exact ((IHn _ _ e1' e2') ←▪).
          - exact ((IHn _ _ e1' e2') ← t2). }
        {   exact ((IHn _ _ e1' e2) ← (e2 ↓ t1)). }
Defined.

Notation  "e1 '•' e2" := (@composeER _ _ _ e1 e2) 
                         (at level 60, right associativity).
          (* \bullet *)

(* example computation
Eval compute in ((□ ←▪ ← F1 ←▪ ← F2 ←▪) • (□ ←▪ ←▪ ← F1)).
*)

Lemma erComposeNN : ∀ {n c d : nat}, ∀ e : ER n c, ∀ e' : ER c d,
        (e ←▪) • (e' ←▪) = ((e • e') ←▪).
Proof.
  trivial.
Defined.

Lemma erComposeNP : ∀ {n c d : nat}, ∀ e : ER n c,
                    ∀ e' : ER c d, ∀ t : Fin.t d,
        (e ←▪) • (e' ← t) = ((e • e') ← t).
Proof.
  intros.
  induction d.
  - apply Fin.case0. exact t.
  - trivial.
Defined.

Lemma erComposeP : ∀ {n c d : nat}, ∀ e : ER n c,
                   ∀ e' : ER c d, ∀ t : Fin.t c,
       (e ← t) • e' = (e • e') ← (e' ↓ t).
Proof.
  intros.
  destruct c.
  - inversion t.
  - destruct n.
    + apply (er0SAbsurd e).
    + destruct d.
      * apply (erS0Absurd e').
      * trivial.
Defined.

(* idRel is left neutral for "•" *)

Lemma idRelLeftNeutral : ∀ {n c : nat}, ∀ e : ER n c, △ • e = e.
Proof.
  induction n; destruct c; intro e.
  - rewrite (er00Empty e). trivial.
  - apply (er0SAbsurd e).
  - apply (erS0Absurd e).
  - destruct (erCase e) as [[e' eq]|[[e' t] eq]];
    rewrite eq; rewrite idRelStructure.
    + rewrite erComposeNN.
      rewrite IHn.
      trivial.
    + unfold fst,snd.
      rewrite erComposeNP.
      rewrite IHn.
      trivial.
Defined.

(* idRel is right neutral for "•" *)

Lemma idRelRightNeutral : ∀ {n c : nat}, ∀ e : ER n c, e • △ = e.
Proof.
  intro n.
  induction n; destruct c; intro e.
  - rewrite (er00Empty e). trivial.
  - apply (er0SAbsurd e).
  - apply (erS0Absurd e).
  - destruct (erCase e) as [[e' eq]|[[e' t] eq]]; 
    rewrite eq; rewrite idRelStructure; 
    [rewrite erComposeNN | rewrite erComposeP]; rewrite IHn.
    + trivial.
    + unfold fst, snd.
      rewrite <- idRelStructure.
      rewrite idRelId.
      trivial.
Defined.

(* erMap of "e1 • e2" is composition of erMaps *)

Lemma erMapCompose : ∀ {n m l : nat}, ∀ e1 : ER n m,
      ∀ e2 : ER m l, ∀ x : Fin.t n,
      (e1 • e2) ↓ x = e2 ↓ (e1 ↓ x).
Proof.
  intro n; induction n.
  { (* n== 0 *)
    intros m l e1 e2 x. inversion x. }
  { (* n > 0 *)
    destruct m.
    - (* m == 0 *) intros l e1. apply (erS0Absurd e1).
    - (* m > 0 *)  destruct l.
      + (* l == 0 *) intros e1 e2. apply (erS0Absurd e2).
      + (* l > 0 *)
        intros e1 e2 x.
        destruct (erCase e1) as [[e1' eq]|[[e1' t1] eq]]; 
        rewrite eq; clear eq.
        { (* e1 = e1' ←▪ *)
          destruct (erCase e2) as [[e2' eq]|[[e2' t2] eq]]; 
          rewrite eq; clear eq.
          - (* e2 = e2' ←▪ *)
            rewrite erComposeNN.
            destruct (finLastOrPrevious x) as [[y eq]|eq]; rewrite eq.
            + (* x = L_R 1 y *)
              rewrite ?erMapNewPrevious. rewrite IHn. trivial.
            + (* x = finLast *)
              rewrite ?erMapNewLast. trivial.
          - (* e2 = e2' ← t2 *)
            unfold fst,snd. rewrite erComposeNP.
            destruct (finLastOrPrevious x) as [[y eq]|eq]; rewrite eq.
            + (* x = L_R 1 y *)
              rewrite erMapPutPrevious. rewrite erMapNewPrevious.
              rewrite erMapPutPrevious. apply IHn.
            + (* x = finLast *)
              rewrite erMapPutLast. rewrite erMapNewLast. 
              rewrite erMapPutLast. trivial. }
      { (* e1 = e1' ← t1 *)
        unfold fst, snd. rewrite erComposeP.
        destruct (finLastOrPrevious x) as [[y eq]|eq]; rewrite eq.
        - (* x = L_R 1 y *)
          rewrite ?erMapPutPrevious. apply IHn.
        - (* x = finLast *)
          rewrite ?erMapPutLast. trivial. }}
Defined.

(* "•" is associative *)

Ltac erRewrites1 i := 
  try repeat  (rewrite erComposeNN) ||
              (rewrite erComposeNP) ||
              (rewrite erComposeP)  ||
              (rewrite erMapCompose)||
              (rewrite i).
Ltac erRewrites2 i :=
  try repeat (rewrite erComposeNN)    ||
             (rewrite erComposeNP)    ||
             (rewrite erComposeP)     ||
             (rewrite <- erMapCompose)||
             (rewrite i).
Ltac erRewrites i := solve [ (erRewrites1 i; trivial) |
                             (erRewrites2 i; trivial) ].

Lemma erComposeAssociative : ∀ {n m l k : nat},
      ∀ e1 : ER n m, ∀ e2 : ER m l, ∀ e3 : ER l k,
      (e1 • e2) • e3 = e1 • e2 • e3.
Proof.
  intro n; induction n.
  - (* n == 0 *) destruct m.
    + (* m == 0 *) destruct l.
      * (* l == 0 *) { destruct k; intros e1 e2 e3.
          - (* k == 0 *) apply er00Empty.
          - (* k > 0  *) apply (er0SAbsurd e3). }
      * (* l > 0 *) intros k e1 e2. apply (er0SAbsurd e2).
    + (* m > 0 *) intros l k e1. apply (er0SAbsurd e1).
  - (* n > 0 *) destruct m; intros l k e1.
    + (* m == 0 *) apply (erS0Absurd e1).
    + (* m > 0  *) destruct l; intro e2.
      * (* l == 0 *) apply (erS0Absurd e2).
      * (* l > 0  *) { intro e3. destruct k.
          - (* k == 0 *) apply (erS0Absurd e3).
          - (* k > 0  *)
            destruct (erCase e1) as [[e1' eq]|[[e1' t1] eq]];
            rewrite eq; clear eq;
            destruct (erCase e2) as [[e2' eq]|[[e2' t2] eq]];
            rewrite eq; clear eq;
            destruct (erCase e3) as [[e3' eq]|[[e3' t3] eq]];
            rewrite eq; clear eq; try (unfold fst,snd);
            erRewrites IHn. }
Defined.

(* order relations on Fin.t *)

Definition to_nat' : ∀ {n : nat}, Fin.t (S n) → nat.
Proof.
  apply (Fin.rectS (λ _ y, nat)).
  - intro. exact 0.
  - intros _ _ toNat'. exact (S toNat').
Defined.

Lemma toNat'Lemma : ∀ {n : nat}, ∀ (x : Fin.t (S n)),
                     to_nat' (FS x) = S (to_nat' x).
Proof.
  trivial.
Defined.

Lemma toNat'LR : ∀ {m : nat}, ∀ (x : Fin.t (S m)),
                 @to_nat' (S m) (L_R 1 x) = to_nat' x.
Proof.
  intro m. induction m.
  - intro x. apply (Fin.caseS' x).
    + trivial.
    + apply Fin.case0.
  - intro x. apply (Fin.caseS' x).
    + trivial.
    + intro p.
      assert (L_R 1 (FS p) = FS (L_R 1 p)) as H by trivial.
      rewrite H. rewrite? toNat'Lemma. 
      rewrite IHm.
      trivial.
Defined.

Definition leF : forall {m n : nat},
                 Fin.t (S m) → Fin.t (S n) → Prop :=
  λ m n x y, to_nat' x ≤ to_nat' y.

Definition ltF : ∀ {m n : nat},
                 Fin.t (S m) → Fin.t (S n) → Prop :=
  λ m n x y, to_nat' x < to_nat' y.

Notation "x ≼ y" := (leF x y) (at level 70).           (* \preceq *)
Notation "x ≺ y" := (ltF x y) (at level 70).           (* \prec   *)
Notation "x ≈ y" := ((x ≼ y) ∧ (y ≼ x)) (at level 70). (* \approx *)

Definition leFDecidable {m n : nat}
               (x : Fin.t (S m)) (y : Fin.t (S n)) :
               {x ≼ y} + {~ (x ≼ y)}.
Proof.
  pose (to_nat' x) as x'.
  pose (to_nat' y) as y'.
  exact (le_dec x' y').
Defined.

Lemma ltTleF {m n : nat} (x : Fin.t (S m)) (y : Fin.t (S n)) :
      x ≺ y ↔ (FS x) ≼ y.
Proof.
  unfold "≺","≼","<".
  rewrite (toNat'Lemma x).
  split; intro; trivial.
Defined.

Lemma eqFLemma {m n : nat} (x : Fin.t (S m)) (y : Fin.t (S n)) :
      x ≈ y ↔ (to_nat' x = to_nat' y).
Proof.
  apply leAntiSymmetric.
Defined. 

Lemma ltFTricho {m n : nat} (x : Fin.t (S m)) (y : Fin.t (S n)) :
      (x ≈ y) + (y ≺ x) + (x ≺ y).
Proof.
  unfold "≺".
  pose (ltTricho (to_nat' x) (to_nat' y)) as tnT.
  destruct tnT as [[Eq | GT ]| LT].
  - left. left.
    exact ((proj2 (eqFLemma x y)) (eq_sym Eq)).
  - left. right. exact GT.
  - right. exact LT.
Defined.

