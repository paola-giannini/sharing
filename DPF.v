Require Import Arith.
Require Import NatMisc.
Require Import Fin.
Require Import Vector.
Require Import FinVectorMisc.
Import VectorNotations.
Require Import SigmaMisc.
Require Import NotationsMisc.
Require Import Omega.
From Equations Require Import Equations.
Set Equations Transparent.
Unset Equations WithK.

(* decidable propositions *)

Definition DecProp : Type := { P : Prop & {P} + {~P} }.

(* funny names for the projections *)
Definition holds : DecProp -> Prop := @projT1 _ _.

Definition decide (P : DecProp) : {holds P} + {~(holds P)} := projT2 P.

Definition dpTrue : DecProp := {| True ; left I |}.

Equations dpNot (P : DecProp) : DecProp :=
  dpNot {| P ; decP |} := {| ~P ; _ |}.
Next Obligation. destruct decP; intuition. Defined.

Definition dpNot1 (P : DecProp) : holds (dpNot P) <-> ~ (holds P).
Proof. destruct P; intuition. Defined.

Definition lem (P : DecProp) : {holds P} + {holds (dpNot P)}.
Proof. destruct P. intuition. Defined.

Definition dpFalse : DecProp := dpNot dpTrue.

Lemma dpFalse1 (P : DecProp) : holds (dpNot P) <-> ~ (holds P).
Proof. destruct P. intuition. Defined.

Equations dpOr (P Q : DecProp) : DecProp :=
  dpOr {| P ; decP |} {| Q ; decQ |} := {| P \/ Q ; _ |}.
Next Obligation. destruct decP; destruct decQ; intuition. Defined.

Lemma dpOr1 (P Q : DecProp) : holds (dpOr P Q) <-> (holds P) \/ (holds Q).
Proof. destruct P; destruct Q; program_simpl. reflexivity. Defined.

Equations dpAnd (P Q : DecProp) : DecProp :=
  dpAnd {| P ; decP |} {| Q ; decQ |} := {| P /\ Q ; _ |}.
Next Obligation. destruct decP; destruct decQ; intuition. Defined.

Lemma dpAnd1 (P Q : DecProp) : holds (dpAnd P Q) <-> (holds P) /\ (holds Q).
Proof. destruct P; destruct Q; program_simpl; reflexivity. Defined.

Equations dpImp (P Q : DecProp) : DecProp :=
  dpImp {| P ; decP |} {| Q ; decQ |} := {| P -> Q ; _ |}.
Next Obligation. destruct decP; destruct decQ; intuition. Defined.

Lemma dpImp1 (P Q : DecProp) : holds (dpImp P Q) <-> (holds P) -> (holds Q).
Proof. destruct P; destruct Q; program_simpl; intuition. Defined.

Lemma dpContra (P Q : DecProp) : 
               holds (dpImp (dpNot P) (dpNot Q)) <-> holds (dpImp Q P).
Proof. destruct P; destruct Q. program_simpl. intuition. Defined.

Equations dpIff (P Q : DecProp) : DecProp :=
  dpIff P Q := dpAnd (dpImp P Q) (dpImp Q P).

Lemma dpIff1 (P Q : DecProp) : 
             holds (dpIff P Q) <-> holds (dpImp P Q) /\ holds (dpImp Q P).
Proof. destruct P; destruct Q; program_simpl; intuition. Defined.

Definition dpFinEq {n : nat} (x y : Fin.t n) : DecProp :=
  {| x = y ; t_eqdec _ x y |}.

Lemma dpFinEq1 {n : nat} (x y : Fin.t n) : holds (dpFinEq x y) <-> x = y.
Proof. intuition. Defined.

Definition dpFinLt {n : nat} (x y : Fin.t n) : DecProp :=
  {| x <~ y ; ltFDecidable x y |}.

Lemma dpFinLt1 {n : nat} (x y : Fin.t n) : holds (dpFinLt x y) <-> x <~ y.
Proof. intuition. Defined.

(* decidable predicates on Fin.t n ... *)

Definition DPF (n : nat) : Type := (Fin.t n) -> DecProp.

Definition InDPF {n : nat} (P : DPF n) (x : Fin.t n) : Prop := holds (P x).

Definition decideInDPF {n : nat} (P : DPF n) (x : Fin.t n) :
                       {InDPF P x} + {~(InDPF P x)} := decide (P x).

Definition emptyDPF {n : nat} : DPF n := fun x => dpFalse.

Lemma emptyDPF1 {n : nat} (x : Fin.t n) : ~ (InDPF emptyDPF x).
Proof. intuition. Defined.

Definition fullDPF {n : nat} : DPF n := fun x => dpTrue.

Lemma fullDPF1 {n : nat} (x : Fin.t n) : InDPF fullDPF x.
Proof. exact I. Defined.

Definition dpfMeet {n : nat} (s1 s2 : DPF n) : DPF n :=
  fun x => dpAnd (s1 x) (s2 x).

Lemma dpfMeet1 {n : nat} (s1 s2 : DPF n) (x : Fin.t n) :
               InDPF (dpfMeet s1 s2) x <-> 
               InDPF s1 x /\ InDPF s2 x.
Proof. unfold InDPF, dpfMeet; rewrite dpAnd1; intuition. Defined.

Definition dpfJoin {n : nat} (s1 s2 : DPF n) : DPF n :=
  fun x => dpOr (s1 x) (s2 x).

Lemma dpfJoin1 {n : nat} (s1 s2 : DPF n) (x : Fin.t n) :
               InDPF (dpfJoin s1 s2) x <->
               InDPF s1 x \/ InDPF s2 x.
Proof. unfold InDPF, dpfJoin; rewrite dpOr1; intuition. Defined.

Definition dpfComplement {n : nat} (s : DPF n) : DPF n :=
  fun x => dpNot (s x).

Lemma dpfComplement1 {n : nat} (s : DPF n) (x : Fin.t n) :
                     InDPF (dpfComplement s) x <-> ~ InDPF s x.
Proof. unfold InDPF, dpfComplement; rewrite dpNot1; intuition. Defined.

Definition dpfShrink {n : nat} (s : DPF (S n)) : DPF n :=
  fun x => s (FS x).

Lemma dpfShrink1 {n : nat} (s : DPF (S n)) (x : Fin.t n) :
                 InDPF s (FS x) <-> InDPF (dpfShrink s) x.
Proof. split; intros; program_simpl. Defined.

Lemma dpfShrinkMeet {n : nat} (s1 s2 : DPF (S n)) (x : Fin.t n) :
                    InDPF (dpfMeet (dpfShrink s1) (dpfShrink s2)) x <->
                    InDPF (dpfShrink (dpfMeet s1 s2)) x.
Proof. intuition. Defined.

Lemma dpfShrinkJoin {n : nat} (s1 s2 : DPF (S n)) (x : Fin.t n) :
                    InDPF (dpfJoin (dpfShrink s1) (dpfShrink s2)) x <->
                    InDPF (dpfShrink (dpfJoin s1 s2)) x.
Proof. intuition. Defined.

Lemma dpfShrinkComplement {n : nat} (s : DPF (S n)) (x : Fin.t n) :
                          InDPF (dpfComplement (dpfShrink s)) x <->
                          InDPF (dpfShrink (dpfComplement s)) x.
Proof. intuition. Defined.

Definition dpfSingle {n : nat} (x : Fin.t n) : DPF n :=
  fun y => dpFinEq x y.

Equations dpfAll {n : nat} (s : DPF n) : DecProp :=
  dpfAll {n:=0}      _  := dpTrue ;
  dpfAll {n:=(S _)}  s  := dpAnd (s F1) (dpfAll (dpfShrink s)).

Equations dpfAny {n : nat} (s : DPF n) : DecProp :=
  dpfAny {n:=0}      _ := dpFalse ;
  dpfAny {n:=(S _)}  s := dpOr (s F1) (dpfAny (dpfShrink s)).

Lemma dpfAnyToWitness {n : nat} {s : DPF n} (any : holds (dpfAny s)) :
                    { x : Fin.t n & InDPF s x }.
Proof.
  induction n.
  - intuition.
  - destruct (decide (dpfAny (dpfShrink s))) as [anyS | notAnyS].
    + destruct (IHn _ anyS); exists (FS x); assumption.
    + destruct (decide (s F1)) as [sF1 | notSF1].
      * exists F1; assumption.
      * rewrite dpfAny_equation_2 in any.
        rewrite dpOr1 in any; apply False_rec; intuition.
Defined.

Lemma dpfWitnessToAny {n : nat} {s : DPF n} (w : {x : Fin.t n & InDPF s x}) :
                      holds (dpfAny s).
Proof.
  induction n.
  - program_simpl; apply Fin.case0; assumption.
  - destruct w; induction x; program_simpl.
    + rewrite dpOr1. intuition.
    + rewrite dpOr1. rewrite dpfShrink1 in i. intuition.
Defined.

Definition dpfNone {n : nat} (s : DPF n) : DecProp :=
  dpNot (dpfAny s).

Equations dpfAbove {n : nat} (x : Fin.t n) : DPF n :=
  dpfAbove {n:=0} x    :=! x;
  dpfAbove {n:=(S _)}  x := fun y => dpFinLt x y.

Lemma dpfAbove1 {n : nat} (x y : Fin.t n) :
                InDPF (dpfAbove x) y <-> x <~ y.
Proof. 
  induction n.
  - apply Fin.case0. assumption.
  - unfold InDPF. program_simpl. intuition.
Defined.

Lemma dpfShrinkAbove {n : nat} (x : Fin.t n) (y : Fin.t n) :
                     InDPF (dpfAbove x) y <->
                     InDPF (dpfShrink (dpfAbove (FS x))) y.
Proof.
  induction n.
  - apply Fin.case0; assumption.
  - repeat rewrite dpfAbove_equation_2.
    unfold dpfShrink, InDPF. repeat rewrite dpFinLt1.
    apply iff_sym.
    apply ltFFS.
Defined.

Lemma dpfShrinkAboveF1 {n : nat} (y : Fin.t n) :
                        InDPF (dpfShrink (dpfAbove F1)) y.
Proof.
  induction n.
  - apply Fin.case0.
  - rewrite <- dpfShrink1.
    rewrite dpfAbove1.
    unfold "<~". 
    rewrite toNat_equation_2. rewrite toNat_equation_3.
    omega.
Defined.

(* dpfNoneAbove s x <=> forall y.  x <~ y -> ~ (s y) *)

Equations dpfNoneAbove {n : nat} (s : DPF n) : DPF n :=
  dpfNoneAbove s := fun x => dpfNone (dpfMeet (dpfAbove x) s).

Lemma dpfShrinkNoneAbove {n : nat} (s : DPF (S n)) (x : Fin.t n) :
                         InDPF (dpfNoneAbove (dpfShrink s)) x <->
                         InDPF (dpfShrink (dpfNoneAbove s)) x.
Proof.
  unfold dpfNoneAbove. repeat rewrite <- dpfShrink1.
  unfold InDPF, dpfNone. repeat rewrite dpNot1. intuition.
  - destruct (dpfAnyToWitness H0).
    rewrite dpfMeet1 in i.
    dependent induction x0.
    + destruct i as [absurd _].
      rewrite dpfAbove1 in absurd.
      exact (notLtF1 absurd).
    + assert (holds (dpfAny (dpfMeet (dpfAbove x) (dpfShrink s)))).
      * apply dpfWitnessToAny. exists x0.
        rewrite dpfMeet1.
        destruct i.
        { split.
          - rewrite dpfAbove1. rewrite <- ltFFS.
            rewrite dpfAbove1 in H1; assumption.
          - exact H2.
        }
      * intuition.
  - destruct (dpfAnyToWitness H0).
    rewrite dpfMeet1 in i.
    assert (holds (dpfAny (dpfMeet (dpfAbove (FS x)) s))).
    + apply dpfWitnessToAny. exists (FS x0).
      rewrite dpfMeet1; destruct i; split.
      * rewrite dpfAbove1. rewrite ltFFS. rewrite dpfAbove1 in H1; assumption.
      * rewrite dpfShrink1; assumption.
    + intuition.
Defined.

Equations dpfMax {n : nat} (s : DPF n) : DPF n :=
  dpfMax s := dpfMeet s (dpfNoneAbove s).

Lemma dpfShrinkMax {n : nat} (s : DPF (S n)) (x : Fin.t n):
                   InDPF (dpfMax (dpfShrink s)) x <->
                   InDPF (dpfShrink (dpfMax s)) x.
Proof. 
  unfold dpfMax.
  rewrite <- dpfShrinkMeet.
  repeat rewrite dpfMeet1.
  rewrite dpfShrinkNoneAbove.
  intuition.
Defined.

Lemma dpfShrinkMaxAny {n : nat} (s : DPF (S n)) :
                      holds (dpfAny (dpfMax (dpfShrink s))) <->
                      holds (dpfAny (dpfShrink (dpfMax s))).
Proof.
  split; intro; apply dpfWitnessToAny; 
  destruct (dpfAnyToWitness H) as [x xP]; exists x.
  - rewrite <- dpfShrinkMax; assumption.
  - rewrite dpfShrinkMax; assumption.
Defined.


Lemma dpfMaxIffAny {n : nat} (s : DPF n) :
                   holds (dpfAny s) <-> holds (dpfAny (dpfMax s)).
Proof.
  induction n; split; program_simpl;
  rewrite dpOr1 in *.
  - destruct (decide (dpfAny (dpfShrink s))).
    + right.
      rewrite (IHn (dpfShrink s)) in h.
      rewrite dpfShrinkMaxAny in h; assumption.
    + left. unfold dpfMax, dpfMeet. rewrite dpAnd1.
      destruct H; split.
      * assumption.
      * unfold dpfNoneAbove, dpfNone.
        rewrite dpNot1.
        intro. apply n0. apply dpfWitnessToAny.
        destruct (dpfAnyToWitness H0).
        rewrite dpfMeet1 in i.
        { destruct i. dependent induction x.
          - apply False_rec.
            rewrite dpfAbove1 in H1. exact (notLtF1 H1).
          - exists x. rewrite <- dpfShrink1; assumption.
        }
      * apply False_rec. exact (n0 H).
      * apply False_rec. exact (n0 H).
  - destruct H.
    + unfold dpfMax, dpfMeet in H. rewrite dpAnd1 in H; intuition.
    + right. 
      rewrite (IHn (dpfShrink s)).
      rewrite dpfShrinkMaxAny; assumption.
Defined.

Lemma dpfMaxOrNone {n : nat} (s : DPF n) :
                   {holds (dpfAny (dpfMax s))} + {holds (dpfNone s)}.
Proof.
  assert ({holds (dpfAny s)} + {holds (dpfNone s)}) by apply lem.
  destruct H.
  + rewrite (dpfMaxIffAny s) in h. intuition.
  + intuition.
Defined.

Lemma dpfMaxWitnessOrNone {n : nat} (s : DPF n) :
                          { x : Fin.t n & InDPF (dpfMax s) x } +
                          {holds (dpfNone s)}.
Proof.
  destruct (dpfMaxOrNone s) as [maxS | noS].
  - left. apply dpfAnyToWitness; assumption.
  - intuition.
Defined.


