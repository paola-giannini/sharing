Require Import Utf8.
Require Import Fin.
Require Import Vector.
From Equations Require Import Equations.
Set Equations Transparent.
Unset Equations WithK.

(* any two elements in Fin.t (1) are equal        *)

Lemma fin1IsProp (x y : Fin.t 1) : x = y.
Proof.
  apply (Fin.caseS' x); apply (Fin.caseS' y).
  - reflexivity.
  - intro impossible; inversion impossible.
  - intro impossible; inversion impossible.
  - intro impossible; inversion impossible.
Qed.


(* a vector of elements of (Fin.t n) of length m
   describes a map (Fin.t m) -> (Fin.t n)   *)

Definition mapOfVect {m n : nat} (v : Vector.t (Fin.t n) m) :
           (Fin.t m) -> (Fin.t n) := fun i => nth v i.

(* operation on vectors inducing composition on corresponding
   maps *)

Definition vectCompose {m n o : nat} 
           (v : Vector.t (Fin.t o) n) 
           (w : Vector.t (Fin.t n) m) : Vector.t (Fin.t o) m :=
           map (mapOfVect v) w.

Lemma mapStepRewrite {A B : Type} {n : nat} 
      (f : A -> B) (v : Vector.t A n) (h : A) :
      map f (cons h v) = cons (f h) (map f v).
Proof.
  reflexivity.
Qed.


Lemma nthMapLemma {A B: Type} {n : nat} (f : A -> B) 
      (w : Vector.t A n) (x : Fin.t n) : 
       nth (map f w) x = f (nth w x).
Proof.
  induction n.
  - inversion x.
  - apply (Fin.caseS' x).
    + apply (Vector.caseS' w).
      reflexivity.
    + apply (Vector.caseS' w).
      intros h v p.
      rewrite (mapStepRewrite f v h).
      assert (forall (C : Type) (o : nat) (k : C)
                 (u : Vector.t C o) (q : Fin.t o), 
                 nth (cons k u) (FS q) = nth u q) 
              as H by reflexivity.
      rewrite (H B).
      rewrite (H A).
      exact (IHn v p).
Qed.

Lemma mapVectComposeIsCompose {m n o : nat}
           (v : Vector.t (Fin.t o) n)
           (w : Vector.t (Fin.t n) m) 
           (x : Fin.t m):
           mapOfVect (vectCompose v w) x = 
           mapOfVect v (mapOfVect w x).
Proof.
  destruct m.
  - (* m = 0 *) inversion x.
  - (* m > 0 *) 
    unfold vectCompose , mapOfVect.
    rewrite nthMapLemma.
    reflexivity.
Qed.

Fixpoint finLast (n : nat) : Fin.t (S n) :=
  match n with
  | 0      => F1
  | (S n') => FS (finLast n')
  end.

Lemma finLastOrPrevious : ∀ {n : nat}, ∀ x : Fin.t (S n),
      { y : Fin.t n | x = L_R 1 y } + { x = finLast n }.
Proof.
  induction n.
  - intro x. right. compute.
    apply (Fin.caseS' x).
    + trivial.
    + apply Fin.case0.
  - intro x.
    apply (Fin.caseS' x).
    + left. exists F1. trivial.
    + intro p. destruct (IHn p) as [[p' eq']| eq'].
      * left. exists (FS p'). rewrite eq'. trivial.
      * right. rewrite eq'. trivial.
Defined.

Lemma shiftinLast : ∀ {n : nat}, ∀ {A : Type},
                    ∀ a : A, ∀ v : Vector.t A n,
                    Vector.nth (shiftin a v) (finLast n) = a.
Proof.
  induction n.
  - intros A a. apply (Vector.case0). trivial.
  - intros B b w. induction w.
    + trivial.
    + apply (IHw IHn).
Defined.

Lemma shiftinPrevious : ∀ {n : nat}, ∀ {A : Type},
                        ∀ a : A, ∀ v : Vector.t A n, ∀ t : Fin.t n,
                        Vector.nth (shiftin a v) (L_R 1 t) =
                          Vector.nth v t.
Proof.
  induction n.
  - intros A a v t. apply (Fin.case0). exact t.
  - intros B b w. induction w.
    + apply (Fin.case0).
    + intro s. apply (Fin.caseS' s).
      * trivial.
      * apply (IHw IHn).
Defined.

(* in order to improve the readability of the elements of ER,
   we interpret the "new" class in ERNew as the largest element
   in Fin.t (S n).
   For this it is convenient to introduce FL, the largest element
   in a Fin.t, and a map FU that just "shifts up" Fin.t n to Fin.t (S n).
   Under the involutive isomorphism invertFin, FL corresponds to F1
   and FU to FS.
*)

Equations FL (n : nat) : Fin.t (S n) :=
FL 0     := F1;
FL (S n) := FS (FL n).

Equations FU {n : nat} (x : Fin.t n) : Fin.t (S n) :=
FU F1     := F1;
FU (FS x) := FS (FU x).

Equations invertFin {n : nat} (x : Fin.t n) : Fin.t n :=
invertFin  F1    := FL _;
invertFin (FS x) := FU (invertFin x).

Lemma invFULemma {n : nat} (x : Fin.t n) :
               invertFin (FU x) = FS (invertFin x).
Proof.
  induction x.
  - rewrite FU_equation_1.
    repeat rewrite invertFin_equation_1.
    apply FL_equation_2.
  - rewrite FU_equation_2.
    rewrite (invertFin_equation_2 (S n) (FU x)).
    rewrite IHx.
    rewrite FU_equation_2.
    rewrite (invertFin_equation_2 n x).
    trivial.
Defined.

Lemma invFLLemma (n : nat) : invertFin (FL n) = F1.
Proof.
  induction n.
  - trivial.
  - rewrite FL_equation_2.
    rewrite invertFin_equation_2.
    rewrite IHn.
    apply FU_equation_1.
Defined.

Lemma invertFinInvolution {n : nat} (x : Fin.t n) : 
           invertFin (invertFin x) = x.
Proof.
  induction x.
  - rewrite invertFin_equation_1.
    apply invFLLemma.
  - rewrite invertFin_equation_2.
    rewrite invFULemma.
    rewrite IHx.
    trivial.
Defined.

Lemma invertFinInjective {n : nat} (x y : Fin.t n) :
        (invertFin x = invertFin y) → x = y.
Proof.
  intro invEq.
  pose (f_equal invertFin invEq) as eq.
  repeat rewrite invertFinInvolution in eq.
  exact eq.
Defined.

Equations shiftinLast' {n : nat} {A : Type} (a : A) (v : Vector.t A n) :
                    Vector.nth (shiftin a v) (FL n) = a :=
shiftinLast' a nil         := eq_refl;
shiftinLast' a (cons _ ws) := eq_trans _ (shiftinLast' a ws).

Equations shiftinPrevious' {n : nat} {A : Type} 
                       (a : A) (v : Vector.t A n) (t : Fin.t n) :
                       Vector.nth (shiftin a v) (FU t) = Vector.nth v t :=
shiftinPrevious' a  nil        t  :=! t;
shiftinPrevious' a (cons _ ws) F1      := eq_refl;
shiftinPrevious' a (cons _ ws) (FS t') := eq_trans _ (shiftinPrevious' a ws _).





