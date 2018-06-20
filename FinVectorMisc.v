Require Import Arith.
Require Import Fin.
Require Import Vector.
Require Import NatMisc.
Import VectorNotations.
Require Import NotationsMisc.
Require Import SigmaMisc.
From Equations Require Import Equations.
Set Equations Transparent.
Unset Equations WithK.

Derive EqDec for Fin.t.

(* any two elements in Fin.t (1) are equal *)

Equations fin1IsProp (x y : Fin.t 1) : x = y :=
  fin1IsProp F1 F1 := eq_refl.

(* a vector v of elements of (Fin.t n) of length m describes 
   a map (Fin.t m) -> (Fin.t n)  *)

Definition mapOfVect {m n : nat} (v : Vector.t (Fin.t n) m) :
                     (Fin.t m) -> (Fin.t n) := nth v.

(* operation on vectors inducing composition on corresponding maps *)

Definition vectCompose {m n o : nat} 
                       (v : Vector.t (Fin.t o) n)
                       (w : Vector.t (Fin.t n) m) :
                        Vector.t (Fin.t o) m :=
  map (nth v) w.

Equations nthMapLemma {A B: Type} {n : nat} (f : A -> B) 
                      (w : Vector.t A n) (x : Fin.t n) :
                      nth (map f w) x = f (nth w x) :=
nthMapLemma f nil x                :=! x;
nthMapLemma f (cons _ ws') F1      := eq_refl;
nthMapLemma f (cons _ ws') (FS x') := nthMapLemma f ws' x'.

(* in order to improve the readability of the elements of ER,
   we interpret the "new" class in ERNew as the largest element
   in Fin.t (S n).
   For this it is convenient to introduce FL, the largest element
   in a Fin.t, and a map FU that just "shifts up" Fin.t n to Fin.t (S n).
   Under the involutive isomorphism invertFin, FL corresponds to F1
   and FU to FS.
*)

Equations FL (n : nat) :
             Fin.t (S n) :=
  FL 0     := F1;
  FL (S n) := FS (FL n).

Equations FU {n : nat} (x : Fin.t n) :
             Fin.t (S n) :=
  FU F1     := F1;
  FU (FS x) := FS (FU x).

Equations invertFin {n : nat} (x : Fin.t n) : 
                    Fin.t n :=
  invertFin  F1    := FL _;
  invertFin (FS x) := FU (invertFin x).

Equations invFULemma {n : nat} (x : Fin.t n) :
                     invertFin (FU x) = FS (invertFin x) :=
  invFULemma F1     := _;
  invFULemma (FS x) := (f_equal _ (invFULemma x)).

Equations invFLLemma (n : nat) :
                     invertFin (FL n) = F1 :=
  invFLLemma 0     := eq_refl;
  invFLLemma (S n) := f_equal FU (invFLLemma n).

(* invertFin is an involution *)

Equations invertFinInv {n : nat} (x : Fin.t n) :
                       invertFin (invertFin x) = x :=
  invertFinInv {n:=0}      x     :=! x;
  invertFinInv {n:=(S _)}  F1    := (invFLLemma _);
  invertFinInv {n:=(S _)} (FS y) := (eq_trans
                                     (invFULemma (invertFin y))
                                     (f_equal _ (invertFinInv y))).

(* in particular, it is injective *)
Equations invertFinInjective {n : nat} (x y : Fin.t n)
                             (invEq: invertFin x = invertFin y) :
                              x = y :=
  invertFinInjective x y eq := x
                                 ={ eq_sym (invertFinInv _) }=
                               invertFin (invertFin x)
                                 ={ f_equal invertFin eq }=
                               invertFin (invertFin y)
                                 ={ invertFinInv _ }=
                               y QED.

(* to use invertFin for pattern matching, we have to keep
   the association ... *)

Definition invFinViewType {n : nat} (x : (Fin.t n)) : Type :=
  { y : Fin.t n & x = invertFin y }.

Definition invFinView {n : nat} (x : (Fin.t n)) : invFinViewType x :=
  {| invertFin x ; eq_sym (invertFinInv x) |}.

(* case splitting according to FU and FL *)

Equations(noind) finFUOrFL {n : nat} (x : Fin.t (S n)) :
                 { y : Fin.t n & x = FU y } + ( x = FL n ) :=
  finFUOrFL  {n:=0}     F1                  := (inr eq_refl);
  finFUOrFL  {n:=(S _)} x with invFinView x := {
                        | {| F1  ; eq |} := (inr eq);
                        | {| FS _; eq |} := (inl {| invertFin _ ; eq |})}.


Equations shiftinLast {n : nat} {A : Type} (a : A) (v : Vector.t A n) :
                      nth (shiftin a v) (FL n) = a :=
  shiftinLast a  []         := eq_refl;
  shiftinLast a (cons _ ws) := eq_trans _ (shiftinLast a ws).

Equations shiftinPrevious {n : nat} {A : Type} (a : A)
                          (v : Vector.t A n) (t : Fin.t n) :
                          nth (shiftin a v) (FU t) = nth v t :=
  shiftinPrevious a  nil         t      :=! t;
  shiftinPrevious a (cons _ ws)  F1     := eq_refl;
  shiftinPrevious a (cons _ ws) (FS t') := eq_trans _ (shiftinPrevious a ws _).


(* these are NoConfusion principles for FL and FU ...
   how to formulate properly ? *)

Lemma finNotFUAndFL {n : nat} (x : Fin.t n) 
                    (eq : FU x = FL n) : False.
Proof.
  induction n.
  - apply (Fin.case0 _ x).
  - pose (f_equal invertFin eq) as eq'. simpl in eq'.
    rewrite invFULemma in eq'.
    rewrite invFLLemma in eq'.
    simpl in eq'.
    inversion eq'.
Defined.

Lemma fuIsInjective {n : nat} (x y : Fin.t n)
                    (eq : FU x = FU y) : x = y.
Proof.
  induction n.
  - apply Fin.case0.
  - apply (f_equal invertFin) in eq.
    repeat rewrite invFULemma in eq.
    inversion eq.
    apply sigmaNat in H0. 
    apply invertFinInjective.
    exact H0.
Defined.



(* order relations on Fin.t *)

Equations toNat {n : nat} (x : Fin.t n) : nat :=
  toNat {n:=0}      x      :=! x;
  toNat {n:=(S _)}  F1     := 0;
  toNat {n:=(S _)} (FS x') := S (toNat x').

Definition leF : forall {m n : nat},
                 Fin.t m -> Fin.t n -> Prop :=
  fun m n x y => toNat x <= toNat y.

Definition ltF : forall {m n : nat},
                 Fin.t m -> Fin.t n -> Prop :=
  fun m n x y => toNat x < toNat y.

Notation "x <=~ y" := (leF x y) (at level 70).
Notation "x <~ y"  := (ltF x y) (at level 70).
Notation "x =~ y"  := ((x <=~ y) /\ (y <=~ x)) (at level 70).

Definition leFDecidable {m n : nat}
                        (x : Fin.t m) (y : Fin.t n) :
                        {x <=~ y} + {~ (x <=~ y)}.
Proof.
  pose (toNat x) as x'.
  pose (toNat y) as y'.
  exact (le_dec x' y').
Defined.

Definition ltFDecidable {m n : nat}
                        (x : Fin.t m) (y : Fin.t n) :
                        {x <~ y} + {~ (x <~ y)}.
Proof.
  pose (toNat x) as x'.
  pose (toNat y) as y'.
  exact (lt_dec x' y').
Defined.

Lemma ltTleF {m n : nat} (x : Fin.t m) (y : Fin.t n) :
              x <~ y <-> (FS x) <=~ y.
Proof.
  unfold "<~","<=~","<".
  destruct m.
  - inversion x.
  - destruct n.
    + inversion y.
    + rewrite toNat_equation_3. intuition.
Defined.

Lemma eqFLemma {m n : nat} (x : Fin.t m) (y : Fin.t n) :
                x =~ y <-> (toNat x = toNat y).
Proof.
  unfold "<=~"; split.
  - apply leAntiSymmetric.
  - intro eq; split; rewrite eq; trivial.
Defined.

Lemma eqFToEq {m : nat} (x y : Fin.t m) :
               x =~ y <-> x = y.
Proof.
  rewrite eqFLemma.
  induction m.
  - apply Fin.case0. assumption.
  - induction x; dependent induction y.
    + intuition.
    + split; intro; apply False_rec.
      * program_simpl.
      * inversion H.
    + split; intro; apply False_rec.
      * program_simpl.
      * inversion H.
    + split; intro; inversion H.
      * rewrite (IHx y) in H1; congruence.
      * rewrite H; reflexivity.
Defined.

Lemma ltFTricho {m n : nat} (x : Fin.t m) (y : Fin.t n) :
      (x =~ y) + (y <~ x) + (x <~ y).
Proof.
  unfold "<~".
  pose (ltTricho (toNat x) (toNat y)) as tnT.
  destruct tnT as [[Eq | GT ]| LT]; intuition.
  pose ((proj2 (eqFLemma x y)) (eq_sym Eq)); intuition.
Defined.

Lemma ltFTricho' {m : nat} (x y : Fin.t m) :
      (x = y) + (y <~ x) + (x <~ y).
Proof.
  destruct (ltFTricho x y).
  - left. destruct s.
    + left. rewrite eqFToEq in a; assumption.
    + right; assumption.
  - right. assumption.
Defined.

Lemma ltFFS {m n : nat} {x : Fin.t m} {y : Fin.t n} :
      ((FS x) <~ (FS y)) <-> (x <~ y).
Proof.
  unfold "<~".
  repeat (rewrite toNat_equation_3).
  split.
  - apply leSN.
  - apply leNS.
Defined.

Lemma ltFFS1 {m n : nat} {x : Fin.t m} {y : Fin.t n} :
      ((FS x) <~ (FS y)) -> (x <~ y).
Proof. rewrite ltFFS. intuition. Defined.

Lemma notLtF1 {m n : nat} {x : Fin.t m} : ~ (x <~ (@F1 n)).
Proof.
  unfold "<~". rewrite toNat_equation_2. apply notLt0.
Defined.

Lemma ltFIrrefl {m : nat} (x : Fin.t m) : ~ (x <~ x).
Proof.
  apply lt_irrefl.
Defined.

Lemma ltFAsymm {m n : nat} (x : Fin.t m) (y : Fin.t n) : x <~ y -> ~ (y <~ x).
Proof. apply Nat.lt_asymm. Defined.

