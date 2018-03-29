Require Import Utf8.
Require Import Decidable.
Require Import Arith.
Require Import NatMisc.
Require Import Fin.
Require Import Vector.
Import VectorNotations.

Fixpoint vectAllFin (n : nat) : Vector.t (Fin.t n) n :=
  match n with
  | O      => nil (Fin.t O)
  | (S n') => cons _ F1 _ (map FS (vectAllFin n'))
  end.


(* Define decidable equivalance relations on Fin.t n as an inductive
   type family. This should make definition of the equivalence closure,
   the join of two equivalence relations a.s.o. easier.

   We define a type family EqRF ("equivalence relations on Fin.t n"),
   indexed by  n and the number of equivalence classes, c.

   There is just the empty relation in EqRF O O. It is built by the 
   constructor EqRFEmpty.

   Given an equivalence relation on Fin.t n, we can interpret this as
   the restriction to F1, ..., (FS^(n-1) F1) of a new equivalence
   relation on Fin.t (S n). To define the latter completely, we just
   have to say whether (FS^n F1) forms an equivalence class of it's
   own (Constructor EqRFNew), or to which of the existing equivalence
   classes it belongs (Constructor EqRFPut).
*)

Inductive EqRF : nat -> nat -> Type :=
  | EqRFEmpty : EqRF O O
  | EqRFNew   : forall {n c : nat}, (EqRF n c) -> 
                EqRF (S n) (S c)
  | EqRFPut   : forall {n c : nat}, Fin.t c ->  EqRF n c -> 
                EqRF (S n) c.

Notation "□"         := EqRFEmpty.
Notation "eqr '←▪'"  := (EqRFNew eqr) (at level 70).
Notation "eqr '←' x" := (EqRFPut x eqr) (at level 69, 
                                          left associativity).

Notation F2 := (FS F1).  Notation F3 := (FS F2).
Notation F4 := (FS F3).  Notation F5 := (FS F4).
Notation F6 := (FS F5).  Notation F7 := (FS F6).
Notation F8 := (FS F7).  Notation F9 := (FS F8).

(* if EqRF n c is inhabited, we have n ≥ c *)

Lemma eqRFle {n c : nat} : EqRF n c → c ≤ n.
Proof.
  apply (EqRF_ind (λ n c, λ e, c ≤ n)).
  - trivial.
  - intros n' c' _ cLEn. exact (leNS cLEn).
  - intros n' c' _ _ cLEn. exact (le_S _ _ cLEn).
Defined.

(* if EqRF n c is inhabited and n ≠ 0, then c ≠ 0 *)

Lemma eqRFcNot0 {n c : nat} : EqRF n c → n ≠ 0 → c ≠ 0.
Proof.
  Print EqRF_rect.
  apply (EqRF_rect (λ n c, λ e, n ≠ 0 → c ≠ 0)).
  - trivial.
  - intros. exact (neqSucc0 c0).
  - intros. intro. rewrite H1 in t.  
    apply (Fin.case0). exact t.
Defined.

(* any element of EqRF 0 0 is equal to □ *)

Lemma eqRF00Empty (e : EqRF 0 0) : e = □.
Proof.
  assert (∀ P : EqRF 0 0 → Prop, (P □) →
         (∀ (e : EqRF 0 0), P e)).
  { (* extract as induction principle ? *)
    intros P caseEmpty.
    (* extend P to a type family on all equivalences in
       order to apply EqRF_rect *)
    pose (λ n : nat, match n as n0 
                   return (∀ c : nat, EqRF n0 c → Prop ) with
          | 0 => λ c : nat, match c  with
               | 0   =>  λ e : (EqRF 0 0), P e
               | (S c') =>  λ e : EqRF _ _, True
               end
          | _ => λ c : nat, λ e : EqRF _ _, True
          end ) as P'.
    apply (EqRF_ind P'); intros; compute; trivial. }
  apply (H (λ e, e = □)). trivial.
Defined.

(* we build the vector of length n, having at the ith position the 
   class of the ith element of Fin n w.r.t. the given equivalence *)

Definition classMapVector {n c : nat} (eqr : EqRF n c) : 
           Vector.t (Fin.t c) n.
Proof.
  apply (EqRF_rect 
        (λ n', λ c', λ eq, Vector.t (Fin.t c') n')).
  - exact (nil (Fin.t 0)). (* EqRFEmpty *)
  - intros m d e v.        (* EqRFNew *)
    exact (shiftin (of_nat_lt (le_n (S d))) (map (L_R 1) v)).
  - intros m d i e v.      (* EqRFPut *)
    exact (shiftin i v).
  - exact eqr.
Defined.

Eval compute in (classMapVector (□ ←▪ ← F1 ←▪ ← F2 ← F1)).
(* representation of [[1,2,5],[3,4,9],[6,8],[7]] *)
Eval compute in 
    (classMapVector (□ ←▪ ← F1 ←▪ ← F2 ← F1 ←▪ ←▪ ← F3 ← F2)).
(*  [[1],[2,4],[3,5,6]] *)
Eval compute in (classMapVector (□ ←▪ ←▪ ←▪ ← F2 ← F3 ← F3)).

(* the identity *)

Definition idRel {n : nat} : EqRF n n.
Proof.
  induction n.
  - exact □.
  - exact (IHn ←▪).
Defined.

(* derivatives ... moved out to EqRFD *)

(* compose Equivalences *)

(* need an induction principle for nontrivial equivalences,
   with □ ←▪ as a base case: *)

Lemma eqRF_rectNonEmpty :
    ∀ P : ∀ n c : nat, EqRF (S n) c → Type,
      (P 0 1 (□ ←▪))
    → (∀ (n c : nat) (e : EqRF (S n) c),
            P n c e → P (S n) (S c) (e ←▪))
    → (∀ (n c : nat) (t : Fin.t c) (e : EqRF (S n) c),
            P n c e → P (S n) c (e ← t))
    → (∀ (n c : nat) (e : EqRF (S n) c), P n c e).
Proof.
  intros P caseId caseNew casePut n c e.
  (* to use EqRF_rect, extend P to a type family Q on 
     all equivalences *)
  pose ((λ m, match m with
              | (S m') => λ d, λ eqr , P m' d eqr
              | 0      => λ d, λ eqr , True
              end) : (∀ m d : nat, EqRF m d → Type)) as Q.
  assert (Q 0 0 □) as caseQEmpty.
    { compute. trivial. }
  assert (∀ (m d : nat) (eqr : EqRF m d),
          Q m d eqr → Q (S m) (S d) (eqr ←▪)) as caseQNew.
    { intro m.
      induction m.
      - intros d eqr _. compute.
        induction d.
        + rewrite (eqRF00Empty eqr). exact caseId.
        + pose ( le_n_0_eq (S d) (eqRFle eqr)) as sEQ0.
          apply False_rect.
          exact (neqSucc0 d (eq_sym sEQ0)).
      - exact (caseNew m). }
  assert (∀ (m d : nat) (t : Fin.t d) (eqr : EqRF m d), 
          Q m d eqr → Q (S m) d (eqr ← t)) as caseQPut.
    { intro m.
      induction m.
      - intros d t eqr. compute.
        induction d.
        + apply (Fin.case0). exact t.
        + pose ( le_n_0_eq (S d) (eqRFle eqr)) as sEQ0.
          apply False_rect.
          exact (neqSucc0 d (eq_sym sEQ0)).
      - exact (casePut m). }
  exact (EqRF_rect Q caseQEmpty caseQNew caseQPut (S n) c e).
Defined.

Lemma eqRF_rectNonEmpty' :
    ∀ P : ∀ n c : nat, EqRF (S n) (S c) → Type,
      (P 0 0 (□ ←▪))
    → (∀ (n c : nat) (e : EqRF (S n) (S c)),
            P n c e → P (S n) (S c) (e ←▪))
    → (∀ (n c : nat) (t : Fin.t (S c)) (e : EqRF (S n) (S c)),
            P n c e → P (S n) c (e ← t))
    → (∀ (n c : nat) (e : EqRF (S n) (S c)), P n c e).
Proof.
  intros P caseId caseNew casePut n c e.
  (* to use EqRF_rect, extend P to a type family Q on 
     all equivalences *)
  pose ((λ m, match m with
              | (S m') => 
                 λ d, match d with
                      | (S d') => λ eqr , P m' d' eqr
                      | 0      => λ eqr, True
                      end
              | 0      => λ d, λ eqr , True
              end) : (∀ m d : nat, EqRF m d → Type)) as Q.
  assert (Q 0 0 □) as caseQEmpty.
    { compute. trivial. }
  assert (∀ (m d : nat) (eqr : EqRF m d),
          Q m d eqr → Q (S m) (S d) (eqr ←▪)) as caseQNew.
    { intro m.
      induction m.
      - intros d eqr _. compute.
        induction d.
        + rewrite (eqRF00Empty eqr). exact caseId.
        + pose ( le_n_0_eq (S d) (eqRFle eqr)) as sEQ0.
          apply False_rect.
          exact (neqSucc0 d (eq_sym sEQ0)).
      - compute.
        induction d.
        + intro eimp.
          intros. apply (False_rect).
          pose (eqRFcNot0 eimp (neqSucc0 m)) as imp.
          exact (imp (eq_refl)).
        + exact (caseNew m d). }
  assert (∀ (m d : nat) (t : Fin.t d) (eqr : EqRF m d), 
          Q m d eqr → Q (S m) d (eqr ← t)) as caseQPut.
    { intro m.
      induction m.
      - intros d t eqr. compute.
        induction d.
        + apply (Fin.case0). exact t.
        + pose ( le_n_0_eq (S d) (eqRFle eqr)) as sEQ0.
          apply False_rect.
          exact (neqSucc0 d (eq_sym sEQ0)).
      - compute.
        induction d.
        + intros _ eimp.
          intros. apply (False_rect).
          pose (eqRFcNot0 eimp (neqSucc0 m)) as imp.
          exact (imp (eq_refl)).
        + exact (casePut m d). }
  exact (EqRF_rect Q caseQEmpty caseQNew caseQPut (S n) (S c) e).
Defined.

Definition eqRFSn0absurd {n : nat} {A : Type} : EqRF (S n) 0 -> A.
Proof.
  intro e.
  apply False_rect.
  exact ((eqRFcNot0 e (neqSucc0 n)) eq_refl).
Defined.

Definition case {n c : nat} (e : EqRF (S n) (S c)) :
                sum { e' | e = (e' ←▪) } 
                    { p  | e = (fst p) ← (snd p) }.
Proof.
  refine ( 
    match e in EqRF (S n) (S c) 
            return sum { e' | e = (e' ←▪) } 
                       { p  | e = (fst p) ← (snd p) } with
         | e' ←▪  => inl (exist _ e' eq_refl)
         | e' ← t => _
         end ).
  - destruct n1.
    + inversion t.
    + right. exists (e', t). reflexivity.
Defined.

Fixpoint composeEqRF {n c d : nat} (e1 : EqRF n c)
                     (e2 : EqRF c d) : EqRF n d.
Proof.
refine (
  (λ n, match n 
        return ∀ c d : nat, EqRF n c → EqRF c d → EqRF n d 
        with
  | 0      => _
  | (S n') => λ c, 
    match c with
    | 0      => _
    | (S c') => λ d,
      match d with
      | 0      => _
      | (S d') => λ e1, λ e2,
         match (case e1, case e2) with
         | (inl (exist _ e1' e1eq), inl (exist _ e2' e2eq))  => 
             (composeEqRF _ _ _ e1' e2') ←▪
         | (inl (exist _ e1' e1eq), inr (exist _ p2 p2eq))   =>
             (composeEqRF _ _ _ e1' (fst p2)) ← (snd p2)
         | (inr (exist _ p1 p1eq),_)     =>
             (composeEqRF _ _ _ (fst p1) e2) ←
                 Vector.nth (classMapVector e2) (snd p1)
         end
      end
    end
  end) n c d e1 e2).
  - intros c' d' e1'.
    rewrite (le0eq0 c' (eqRFle e1')).
    intro e2'.
    rewrite (le0eq0 d' (eqRFle e2')).
    exact (□).
  - intros d' e1'.
    apply (eqRFSn0absurd e1').
  - intros _ e2'.
    apply (eqRFSn0absurd e2').
Defined.

Eval compute in (composeEqRF (□ ←▪ ← F1 ←▪ ← F2 ←▪) (□ ←▪ ←▪ ← F1)).


(* order relations on Fin.t *)

Definition to_nat' : ∀ {n : nat}, ∀ (x : Fin.t (S n)), nat.
Proof.
  apply (Fin.rectS (λ _ y, nat)).
  - intro. exact 0.
  - intros _ _ toNat. exact (S toNat).
Defined.

Lemma toNat'Lemma : ∀ {n : nat}, ∀ (x : Fin.t (S n)),
                     to_nat' (FS x) = S (to_nat' x).
Proof.
  trivial.
Defined.

Definition leF : forall {m n : nat}, 
                 Fin.t (S m) → Fin.t (S n) → Prop :=
  λ m n x y, to_nat' x ≤ to_nat' y.

Definition ltF : ∀ {m n : nat},
                 Fin.t (S m) → Fin.t (S n) → Prop :=
  λ m n x y, to_nat' x < to_nat' y.

Notation "x ≼ y" := (leF x y) (at level 70).
Notation "x ≺ y" := (ltF x y) (at level 70).
Notation "x ≈ y" := ((x ≼ y) ∧ (y ≼ x)) (at level 70).

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
  unfold "≺".
  unfold "≼".
  unfold "<".
  rewrite (toNat'Lemma x).
  split; intro; trivial.
Defined.






