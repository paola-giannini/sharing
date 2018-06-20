Require Import Arith.
Require Import NatMisc.
Require Import DecidableEquivalences.
Require Import Fin.
Require Import Vector.
Require Import FinVectorMisc.
Import VectorNotations.
Require Import SigmaMisc.
Require Import NotationsMisc.
Require Import DPF.
Require Import EqR.
From Equations Require Import Equations.
Set Equations Transparent.
Unset Equations WithK.

(* meet *)

(* preparations *)

(* w.r.t. an equivalence contained in some [+> e1] the class of [F1] is a
   singleton *)
Lemma eqrContainedInNewF1 {n c1 : nat} (e : EqR (S n)) (e1 : ER n c1) 
                          (cont : e C= {|_; +> e1|}) :
                          e @@ F1 = F1.
Proof.
  destruct e as [c e].
  dependent destruction e.
  - simp eqr.
  - handleFinCase0 c.
    apply False_rect.
    pose (eqrContainsToEqrMaxMapCondition _ _ cont F1) as mmcF1.
    rewrite eqrToDecEqCompute in mmcF1.
    simp eqr in mmcF1.
    inversion mmcF1.
Defined.


(* the smallest equivalence connecting two given elements in Fin.t n *)

(* first in case when x <~ y *)
Equations eqrLtPair {n : nat} (x y : Fin.t n) (xLty : x <~ y) : EqR n :=
  eqrLtPair  {n:=0}      x      _     _   :=! x;
  eqrLtPair  {n:=(S _)}  _      F1    lt  := match (notLtF1 lt) with end;
  eqrLtPair  {n:=(S _)}  F1    (FS y) _   := eqrPut idEqr y;
  eqrLtPair  {n:=(S _)} (FS x) (FS y) lt  := eqrNew (eqrLtPair x y (ltFFS1 lt)).


(* in [eqrLtPair F1 y], the classmax of F1 is y *)
Lemma eqrLtPairF1F1 {n : nat} (y : Fin.t (S n)) (lt : (@F1 (S n)) <~ y) :
                    (eqrLtPair F1 y lt) @@ F1 = y.
Proof.
  funelim (eqrLtPair F1 y lt).
  - pose (notLtF1 lt); intuition.
  - simp eqr.
Defined.
Hint Rewrite @eqrLtPairF1F1 : eqr.

(* the shrink of [eqrLtPair F1 y] is the identity relation *)
Lemma eqrLtPairF1Shrink {n : nat} (y : Fin.t (S n)) (lt : (@F1 (S n)) <~ y) :
                        eqrShrink (eqrLtPair F1 y lt) = idEqr.
Proof.
 dependent destruction y.
 + pose (notLtF1 lt); intuition.
 + program_simpl.
Defined.
Hint Rewrite @eqrLtPairF1Shrink : eqr.

Lemma eqrLtPairF1FS {n : nat} (x : Fin.t n) (y : Fin.t (S n)) (lt : (@F1 (S n)) <~ y) :
                    (eqrLtPair F1 y lt) @@ (FS x) = (FS x).
Proof.
  rewrite <- eqrShrinkClassMax.
  rewrite eqrLtPairF1Shrink.
  simp eqr.
Defined.

(* w.r.t. [eqrLtPair x y], x and y are connected *)
Lemma eqrLtPairPairs {n : nat} (x y : Fin.t n) (lt: x <~ y) :
                     x ~(eqrLtPair x y lt)~ y.
Proof.
  funelim (eqrLtPair x y lt).
  - pose (notLtF1 xLty); intuition.
  - simp eqr.
  - destruct (eqrLtPair t1 t0 (ltFFS1 xLty)); simp eqr; simp eqr in H.
    rewrite H; reflexivity.
Defined.

(* if some equivalence e contains [eqrLtPair x y], it connects x and y *)
Lemma eqrLtPairProp1 {n : nat} (e : EqR n) (x y : Fin.t n) (xLty : x <~ y) :
                     (eqrLtPair x y xLty) C= e  ->  x ~(e)~ y.
Proof.
  destruct e as [c e]. destruct 1; simp eqr. simpl in e0.
  rewrite <- e0; simp eqr.
  pose (eqrLtPairPairs x y xLty) as p; simp eqr in p.
  rewrite p; reflexivity.
Defined.

(* if some equivalence connects x and y, it contains [eqrLtPair x y] *)
Lemma eqrLtPairProp2 {n : nat} (e : EqR n) (x y : Fin.t n) (xLty : x <~ y) :
                     x ~(e)~ y -> (eqrLtPair x y xLty) C= e.
Proof.
  intro xEy. simp eqr in xEy.
  induction n.
  - simp eqr; apply (allEqrMax (eqrLtPair x y xLty)).
  - apply eqrBuildContains; dependent destruction x; simp eqr; intuition.
    + apply idEqrMin.
    + dependent destruction y.
      * pose (notLtF1 xLty); intuition.
      * rewrite eqrLtPair_equation_4. simp eqr. apply IHn.
        assert (e @@ FS x = e @@ FS y) by simp eqr.
        assert ((eqrShrink e) @@ x = (eqrShrink e) @@ y).
        { repeat rewrite <- eqrShrinkClassMax in H. apply FS_inj; assumption. }
        simp eqr in H0.
    + rewrite <- erClassMaxExpand.
      rewrite <- eqrClassMaxCompute.
      rewrite sigmaEqCompute.
      dependent destruction y.
      * pose (notLtF1 xLty); intuition.
      * rewrite eqrLtPair_equation_4; simp eqr.
Defined.

(* really necessary ?? *)
Lemma eqrLtPairIndependentOfLtProof 
           {n : nat} (x y : Fin.t n) (l1 l2 : x <~ y) :
           eqrLtPair x y l1 = eqrLtPair x y l2.
Proof.
  funelim (eqrLtPair x y l1).
  - apply False_rec. exact (notLtF1 l2).
  - funelim (eqrLtPair F1 (FS t0) l2); reflexivity.
  - funelim (eqrLtPair (FS t1) (FS t0) l2).
    rewrite (H1 (ltFFS1 l2)); reflexivity.
Defined.

(* general case *)

Equations eqrPair {n : nat} (x y : Fin.t n) : EqR n :=
  eqrPair x y with (ltFTricho' x y) := {
                   | (inl (inl eq))   := idEqr;
                   | (inl (inr yLtx)) := (eqrLtPair _ _ yLtx);
                   | (inr xLty)       := (eqrLtPair _ _ xLty)}.

(* [eqrPair x y ] is the identity relation *)
Lemma eqrPairxxId {n : nat} (x : Fin.t n) :
                  eqrPair x x = idEqr.
Proof.
  funelim (eqrPair x x).
  - reflexivity.
  - apply False_rec. apply (ltFIrrefl _ l).
  - apply False_rec. apply (ltFIrrefl _ l).
Defined.

(* [eqrPair x y] is equal to [eqrPair y x] *)
Lemma eqrPairUnordered {n : nat} (x y : Fin.t n) :
                       eqrPair x y = eqrPair y x.
Proof.
  funelim (eqrPair x y).
  - rewrite (eqrPairxxId y); reflexivity.
  - funelim (eqrPair y x).
    + apply False_rec. apply (ltFIrrefl _ l).
    + apply False_rec. apply (ltFAsymm _ _ l l0).
    + apply eqrLtPairIndependentOfLtProof.
  - funelim (eqrPair y x).
    + apply False_rec. apply (ltFIrrefl _ l).
    + apply eqrLtPairIndependentOfLtProof.
    + apply False_rec. apply (ltFAsymm _ _ l l0).
Defined.

Lemma eqrPairPairs {n : nat} (x y : Fin.t n) :
                    x ~(eqrPair x y)~ y.
Proof.
  funelim (eqrPair x y).
  - simp eqr.
  - rewrite eqrToDecEqCompute; apply eq_sym; rewrite <- eqrToDecEqCompute.
    apply eqrLtPairPairs.
  - apply eqrLtPairPairs.
Defined.

(* should go up *)
Lemma eqrToDecEqSymmetric {n : nat} (e : EqR n) (x y : Fin.t n) :
                          x ~(e)~ y -> y ~(e)~ x.
Proof.
  intro xEy.
  rewrite eqrToDecEqCompute; apply eq_sym; rewrite <- eqrToDecEqCompute.
  assumption.
Defined.

Lemma eqrPairProp1 {n : nat} (e : EqR n) (x y : Fin.t n) :
                   (eqrPair x y) C= e  ->  x ~(e)~ y.
Proof.
  funelim (eqrPair x y); intro eqrLtCont.
  - simp eqr.
  - apply eqrToDecEqSymmetric.
    apply (eqrLtPairProp1 e y x l eqrLtCont).
  - apply (eqrLtPairProp1 e x y l eqrLtCont).
Defined.

(*
Lemma eqrPairProp2 {n : nat} (e : EqR n) (x y : Fin.t n) :
                   x ~(e)~ y -> (eqrPair x y) C= e.
Proof.
  destruct (ltFTricho' x y) as [[eq | yLtx] | xLty].
  - intro; rewrite eq; rewrite eqrPairxxId; apply idEqrMin.
  - intro xEy.
    apply eqrToDecEqSymmetric in xEy.
    rewrite eqrPairUnordered.
    ***

(* classDPF *)

Equations eqrClassDPF {n : nat} (e : EqR n) (x : Fin.t n) : DPF n :=
  eqrClassDPF e x := fun y => {| e @@ x = e @@ y ;
                                 t_eqdec _ (e @@ x) (e @@ y) |}.




Obligation Tactic := repeat (simp eqr || program_simpl).


Equations eqrMeet (n : nat) (e1 e2 : EqR n) :
                  { e : EqR n & ( (e C= e1) * (e C= e2) * 
                                   forall e' : EqR n,
                                          e' C= e1 -> e' C= e2 -> 
                                          e' C= e )%type } :=
eqrMeet n e1 e2 by rec n lt :=
eqrMeet  0     {|_;#    |} {|_; #    |}     := {| {|0;#|} ; _ |};
eqrMeet (S _)  {|_;+>e1 |} {|_; +>e2 |}
        with (eqrMeet _ {|_;e1|} {|_;e2|})  := {
              | {|{|d3;e3|} ; (c1,c2,uni)|} := {|{|_; +>e3|}; _|} };
eqrMeet (S _) {|_;t1>>e1|} {|_; +>e2 |}
        with (eqrMeet _ {|_;e1|} {|_;e2|})  := {
              | {|{|d3;e3|} ; (c1,c2,uni)|} := {|{|_; +>e3|}; _|} };
eqrMeet (S _) {|_;+>e1  |} {|_;t2>>e2|}
        with (eqrMeet _ {|_;e1|} {|_;e2|})  := {
              | {|{|d3;e3|} ; (c1,c2,uni)|} := {|{|_; +> e3|}; _|} };
eqrMeet (S _) {|_;t1>>e1|} {|_;t2>>e2|}
        with (eqrMeet _ {|_;e1|} {|_;e2|})  := {
              | {|{|d3;e3|} ; (c1,c2,uni)|} with 
                dpfMaxWitnessOrNone (dpfMeet (eqrClassDPF {| _ ; e1 |} (e1 @^ t1))
                                       (eqrClassDPF {| _ ; e2 |} (e2 @^ t2))) := {
                | (inleft  {|x ; xProp|}) := {|{|_; (e3 @v x)>>e3|}; _|};
                | (inright notXProp)      := {|{|_; +> e3 |}; _ |}
              }}.
Next Obligation.
  split.
  - split; exact (idEqrMin _).
  - intro e.
    assert (e = idEqr) as eq by (apply eqr0Id).
    intros _ _. rewrite eq. apply idEqrMin.
Defined.
Next Obligation.
  clear eqrMeet.
  split.
  - split; apply eqrBuildContains; repeat (simp eqr || assumption).
  - intros e4 e4In1 e4In2.
    apply eqrBuildContains.
    + exact (uni (eqrShrink e4) (eqrShrinkPreservesContains _ _ e4In1)
                                (eqrShrinkPreservesContains _ _ e4In2)).
    + assert (e4 @@ F1 = F1) as eq by (apply (eqrContainedInNewF1 _ _ e4In1)).
      rewrite eq; reflexivity.
Defined.
Next Obligation.
  clear eqrMeet.
  split.
  - split; apply eqrBuildContains; repeat (simp eqr || assumption).
  - intros e4 e4In1 e4In2; apply eqrBuildContains.
    + exact (uni (eqrShrink e4) (eqrShrinkPreservesContains _ _ e4In1)
                                (eqrShrinkPreservesContains _ _ e4In2)).
    + assert (e4 @@ F1 = F1) as eq by (apply (eqrContainedInNewF1 _ _ e4In1)).
      rewrite eq; reflexivity.
Defined.
Next Obligation.
  clear eqrMeet.
  split.
  - split; apply eqrBuildContains; repeat (simp eqr || assumption).
  - intros e4 e4In1 e4In2; apply eqrBuildContains.
    + exact (uni (eqrShrink e4) (eqrShrinkPreservesContains _ _ e4In1)
                                (eqrShrinkPreservesContains _ _ e4In2)).
    + assert (e4 @@ F1 = F1) as eq by (apply (eqrContainedInNewF1 _ _ e4In2)).
      rewrite eq; reflexivity.
Defined.
Next Obligation.
  clear eqrMeet.
  rename wildcard62 into n.
  rename wildcard60 into m1.
  rename wildcard63 into m2.
  handleFinCase0 m1.
  handleFinCase0 m2.
  unfold dpfMax in xProp. rewrite dpfMeet1 in xProp.
  destruct xProp as [xInClasses xIsMax].
  rewrite dpfMeet1 in xInClasses. unfold InDPF, holds, eqrClassDPF in xInClasses.
  simpl in xInClasses. simp eqr in xInClasses.
  destruct xInClasses as [t1E1X t2E2X].
  simp eqr in *.
  split.
  - split; apply eqrBuildContains.
    + exact c1.
    + simp eqr.
      pose ((eqrContainsToEqrMaxMapCondition _ _ c1) x) as eq.
      simp eqr in eq.
      rewrite eq. rewrite t1E1X. reflexivity.
    + exact c2.
    + simp eqr.
      pose ((eqrContainsToEqrMaxMapCondition _ _ c2) x) as eq.
      simp eqr in eq.
      rewrite eq. rewrite t2E2X. reflexivity.
  - intros e4 e4In1 e4In2; apply eqrBuildContains.
    + exact (uni (eqrShrink e4) (eqrShrinkPreservesContains _ _ e4In1)
                                (eqrShrinkPreservesContains _ _ e4In2)).
    + destruct e4 as [d4 e4]; dependent destruction e4.
      * simp eqr.
      * handleFinCase0 c.
        (*
        apply eq_sym.
        rewrite <- eqrToDecEqCompute.
        assert ((@F1 (S n)) <~ ({|S c; t >> e4|} @@ F1)).
        { simp eqr. unfold "<~". compute. apply leNS. apply le0n. }
        apply (eqrPairProp1 _ F1 ({|S c; t >> e4|} @@ F1) H).
        *)
        pose ((eqrContainsToEqrMaxMapCondition _ _ e4In1) F1) as eq1;
        simp eqr in eq1; apply FS_inj in eq1; rewrite t1E1X in eq1.
        pose ((eqrContainsToEqrMaxMapCondition _ _ e4In2) F1) as eq2;
        simp eqr in eq2; apply FS_inj in eq2; rewrite t2E2X in eq2.
        simp eqr; apply f_equal.
Admitted.
Next Obligation.
  admit.
Admitted.



*)