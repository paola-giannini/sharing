Require Import Utf8.
Require Import Decidable.
Require Import NatMisc.
Require Import Fin.
Require Import Vector.
Import VectorNotations.



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