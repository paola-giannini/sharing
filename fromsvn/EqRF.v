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
  | ERNew   : forall {n c : nat},           ER n c -> ER (S n) (S c)
  | ERPut   : forall {n c : nat}, Fin.t c -> ER n c -> ER (S n)  c.

Notation F2 := (FS F1).  Notation F3 := (FS F2).
Notation F4 := (FS F3).  Notation F5 := (FS F4).
Notation F6 := (FS F5).  Notation F7 := (FS F6).
Notation F8 := (FS F7).  Notation F9 := (FS F8).

(* if ER n c is inhabited, then n ≥ c *)

Lemma erCLeN : forall {n c : nat}, ER n c -> c <= n.
Proof.
  induction 1.
  - trivial.
  - apply leNS; trivial.
  - apply le_S; trivial.
Defined.

(* if ER n c is inhabited and n <> 0, then c <> 0 *)

Lemma erCNot0 : forall {n c : nat}, ER n c -> n <> 0 -> c <> 0.
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

Lemma erS0Absurd : forall {n : nat} {A : Type}, 
             ER (S n) 0 -> A.
Proof.
  intros n A e.
  apply False_rect.
  exact ((erCNot0 e (neqSucc0 n)) eq_refl).
Defined.

Lemma er0SAbsurd : forall {c : nat} {A : Type}, 
             ER 0 (S c) -> A.
Proof.
  intros c A e.
  apply False_rect.
  apply (neqSucc0 c).
  exact (le0eq0 _ (erCLeN e)).
Defined.

(* to prove something for all elements of ER 0 0, it
   is enough to prove it for EREmpty *)

Lemma er00_rect : forall P : ER 0 0 -> Type, (P EREmpty) ->
                  forall (e : ER 0 0), P e.
Proof.
  intros P caseEmpty.
  (* extend P to a type family on all equivalences so
     ER_rect applies *)
  pose (fun n => fun c =>
    match (n, c) as p return ER (fst p) (snd p) -> Type with
    | (0, 0)  => fun e => P e
    | _       => fun e => True
    end ) as P'.
  apply (ER_rect P'); intros; compute; trivial.
Defined.

(* in particular, any element of ER 0 0 is equal to EREmpty *)

Lemma er00Empty (e : ER 0 0) : e = EREmpty.
Proof.
  apply (er00_rect (fun e => e = EREmpty)).
  trivial.
Defined.

(* elements of ER (S n) (S c) are built as (ERNew e') or (ERPut t e').
   In most situations, destructing (erCase e) works better than
   pattern matching on e *)

Definition erCase {n c : nat} (e : ER (S n) (S c)) :
                sum { e' | e = ERNew e' }
                    { p  | e = ERPut (snd p) (fst p)}.
Proof.
  refine ( 
    match e in ER (S n) (S c)
            return sum { e' | e = ERNew e' }
                       { p  | e = ERPut (snd p) (fst p) } with
         | ERNew e'   => inl (exist _ e' eq_refl)
         | ERPut t e' => _
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

Definition erMapVector : forall {n c : nat},
              ER n c -> Vector.t (Fin.t c) n.
Proof.
  induction 1.
  - (* case EREmpty *)
    exact nil.
  - (* case ERNew _ *)
    exact (shiftin (FL c) (map FU IHER)).
  - (* case ERPut t _ *)
    exact (shiftin t IHER).
Defined.

Notation "e '@@' t" := (Vector.nth (erMapVector e) t) (at level 5).
                                               (* \downarrow *)

(* example computations ...
Eval compute in (erMapVector (□ ←▪ ← F1 ←▪ ← F2 ← F1)).
(* representation of [[1,2,5],[3,4,9],[6,8],[7]] *)
Eval compute in 
    (erMapVector (□ ←▪ ← F1 ←▪ ← F2 ← F1 ←▪ ←▪ ← F3 ← F2)).
(*  [[1],[2,4],[3,5,6]] *)
Eval compute in (erMapVector (□ ←▪ ←▪ ←▪ ← F2 ← F3 ← F3)).
*)

(* one step computation rules for nth (erMapVector _) _  *)

Definition erMapNewLast : forall {n c : nat}, forall e : ER n c,
           (ERNew e) @@ (FL n) = FL c.
Proof.
  intros n c e.
  apply shiftinLast.
Defined.

Definition erMapNewPrevious : forall {n c : nat}, forall e : ER n c,
                              forall x : Fin.t n,
           (ERNew e) @@ (FU x) = FU (e @@ x).
Proof.
  intros n c e x.
  replace ((ERNew e) @@ (FU x)) with
          (nth
            (shiftin (FL c) (map FU (erMapVector e)))
            (FU x)) by trivial.
  rewrite (shiftinPrevious (FL c)
                           (map FU (erMapVector e)) x).
  apply (nthMapLemma).
Defined.

Definition erMapPutLast : forall {n c : nat}, forall e : ER n c,
                          forall x : Fin.t c,
           (ERPut x e) @@ (FL n) = x.
Proof.
  intros n c e x.
  apply shiftinLast.
Defined.

Definition erMapPutPrevious : forall {n c : nat}, forall e : ER n c,
                              forall x : Fin.t c, forall y : Fin.t n,
           (ERPut x e) @@ (FU y) = e @@ y.
Proof.
  intros n c e x y.
  replace ((ERPut x e) @@ (FU y)) with
          (nth
            (shiftin x (erMapVector e))
            (FU y)) by trivial.
  apply (shiftinPrevious x (erMapVector e) y).
Defined.

(* the identity relation *)

Definition idRel {n : nat} : ER n n.
Proof.
  induction n.
  - exact EREmpty.
  - exact (ERNew IHn).
Defined.

(* idRel n is the only element of ER n n *)

Lemma ernnIdRel : forall {n : nat}, forall e : ER n n, e = idRel.
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

(* idRel = (ERNew idRel) *)

Lemma idRelStructure : forall {n : nat}, @idRel (S n) = ERNew idRel.
Proof.
  trivial.
Defined.

(* erMap of idRel is the identity *)

Lemma idRelId : forall {n : nat}, forall x : Fin.t n, 
                idRel @@ x = x.
Proof.
  induction n.
  - inversion x.
  - intro x.
    rewrite idRelStructure.
    destruct (finFUOrFL x) as [[y eq]|eq]; rewrite eq.
    + rewrite erMapNewPrevious.
      rewrite IHn.
      trivial.
    + apply erMapNewLast.
Defined.

(* compose equivalences *)

Definition erCompose {n : nat} : forall {c d : nat},
                   ER n c -> ER c d -> ER n d.
Proof.
  induction n.
  - intros c d e1 e2.
    rewrite (le0eq0 c (erCLeN e1)) in e2.
    rewrite (le0eq0 d (erCLeN e2)).
    exact EREmpty.
  - destruct c.
    + intros d e1. apply (erS0Absurd e1).
    + destruct d.
      * intro. apply erS0Absurd.
      * intros e1 e2.
        destruct (erCase e1) as [[e1' _]|[[e1' t1] _]].
        { destruct (erCase e2) as [[e2' _]|[[e2' t2] _]].
          - exact (ERNew (IHn _ _ e1' e2')).
          - exact (ERPut t2 (IHn _ _ e1' e2')). }
        {   exact (ERPut (e2 @@ t1)
                         (IHn _ _ e1' e2)). }
Defined.

Notation  "e1 '**' e2" := (@erCompose _ _ _ e1 e2) 
                         (at level 60, right associativity).

(* example computation
Eval compute in ((□ ←▪ ← F1 ←▪ ← F2 ←▪) ** (□ ←▪ ←▪ ← F1)).
*)

Lemma erComposeNN {n c d : nat} (e : ER n c) (e' : ER c d) :
                  (ERNew e) ** (ERNew e') = ERNew (e ** e').
Proof.
  trivial.
Defined.

Lemma erComposeNP {n c d : nat} (e : ER n c)
                  (e' : ER c d) (x : Fin.t d) :
                  (ERNew e) ** (ERPut x e') = ERPut x (e ** e').
Proof.
  induction d.
  - apply Fin.case0. exact x.
  - trivial.
Defined.

Lemma erComposeP {n c d : nat} (e : ER n c)
                 (e' : ER c d) (x : Fin.t c) :
                 (ERPut x e) ** e' = ERPut (e' @@ x) (e ** e').
Proof.
  destruct c.
  - inversion x.
  - destruct n.
    + apply (er0SAbsurd e).
    + destruct d.
      * apply (erS0Absurd e').
      * trivial.
Defined.

(* idRel is left neutral for erCompose *)

Lemma idRelLeftNeutral : forall {n c : nat}, forall e : ER n c,
                         idRel ** e = e.
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
    + unfold fst, snd.
      rewrite erComposeNP.
      rewrite IHn.
      trivial.
Defined.

(* idRel is right neutral for erCompose *)

Lemma idRelRightNeutral : forall {n c : nat}, forall e : ER n c, 
                          e ** idRel = e.
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

(* erMap of (erCompose e1 e2) is composition of erMaps *)

Lemma erMapCompose : forall {n m l : nat}, forall e1 : ER n m,
      forall e2 : ER m l, forall x : Fin.t n,
      (e1 ** e2) @@ x = e2 @@ (e1 @@ x).
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
        { (* e1 = ERNew e1' *)
          destruct (erCase e2) as [[e2' eq]|[[e2' t2] eq]]; 
          rewrite eq; clear eq.
          - (* e2 = ERNew e2' *)
            rewrite erComposeNN.
            destruct (finFUOrFL x) as [[y eq]|eq]; rewrite eq.
            + (* x = FU y *)
              rewrite ?erMapNewPrevious. rewrite IHn. trivial.
            + (* x = FL *)
              rewrite ?erMapNewLast. trivial.
          - (* e2 = ERPut t2 e2' *)
            unfold fst,snd. rewrite erComposeNP.
            destruct (finFUOrFL x) as [[y eq]|eq]; rewrite eq.
            + (* x = FU y *)
              rewrite erMapPutPrevious. rewrite erMapNewPrevious.
              rewrite erMapPutPrevious. apply IHn.
            + (* x = FL *)
              rewrite erMapPutLast. rewrite erMapNewLast. 
              rewrite erMapPutLast. trivial. }
      { (* e1 = ERPut t1 e1' *)
        unfold fst, snd. rewrite erComposeP.
        destruct (finFUOrFL x) as [[y eq]|eq]; rewrite eq.
        - (* x = FU y *)
          rewrite ?erMapPutPrevious. apply IHn.
        - (* x = FL *)
          rewrite ?erMapPutLast. trivial. }}
Defined.

(* erCompose is associative *)

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

Lemma erComposeAssociative : forall {n m l k : nat},
      forall e1 : ER n m, forall e2 : ER m l, forall e3 : ER l k,
      erCompose (erCompose e1 e2) e3 = erCompose e1 (erCompose e2 e3).
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


