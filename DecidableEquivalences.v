Require Import Fin.
Require Import Vector.
Require Import Relations_1.
Require Import Decidable.
Require Import FinVectorMisc.


(* decidability of a relation *)

Definition isDecidable {A : Type} (R : Relation A) : Type :=
  forall (x y : A), {R x y} + {~ (R x y)}.

(* type of decidable equivalence relations on a given type *)

Open Scope type_scope. (* allows using _ * _ for cartesian product *)

Definition DecidableEquivalence (A : Type) : Type :=
  { R : Relation A   &   Equivalence _ R * isDecidable R }.

(* projections of components *)

Definition relationOfDecidableEquivalence
           {A : Type} (DER : DecidableEquivalence A) :
           Relation A :=
  projT1 DER.

Definition decidableEquivalenceReflexive
           {A : Type} (DER : DecidableEquivalence A) : 
           Reflexive _ (relationOfDecidableEquivalence DER) :=
  match (fst (projT2 DER)) with
  | Definition_of_equivalence _ _ r _ _ => r
  end.

Definition decidableEquivalenceTransitive
           {A : Type} (DER : DecidableEquivalence A) :
           Transitive _ (relationOfDecidableEquivalence DER) :=
  match (fst (projT2 DER)) with
  | Definition_of_equivalence _ _ _ t _ => t
  end.

Definition decidableEquivalenceSymmetric
           {A : Type} (DER : DecidableEquivalence A) : 
           Symmetric _ (relationOfDecidableEquivalence DER) :=
  match (fst (projT2 DER)) with
  | Definition_of_equivalence _ _ _ _ s => s
  end.

Definition decidableEquivalenceDecidable
           {A : Type} (DER : DecidableEquivalence A) :
           isDecidable (relationOfDecidableEquivalence DER) :=
  snd (projT2 DER).

(* containment and equality of decidable equivalence relations
   are just those of the underlying relations *)

Definition decidableEquivalenceContains
           {A : Type} (DER1 DER2 : DecidableEquivalence A) : Prop :=
  contains _ (projT1 DER1) (projT1 DER2).

Notation "D 'c=' E" := (decidableEquivalenceContains E D)
    (no associativity, at level 70) : decidableEquivalence_scope.
    (* \subseteq *)

Open Scope decidableEquivalence_scope.

(* c= is reflexive *)

Lemma decidableEquivalenceContainsReflexive
      {A : Type} (DER : DecidableEquivalence A) :
      DER c= DER.
Proof.
  intros x y xRy; assumption.
Qed.

(* c= is transitive *)

Lemma decidableEquivalenceContainsTransitive
      {A : Type} (DER1 DER2 DER3 : DecidableEquivalence A) :
      DER1 c= DER2  /\  DER2 c= DER3  ->  DER1 c= DER3.
Proof.
  intros c12andc23 x y xR1y; destruct c12andc23; intuition.
Qed.

Definition decidableEquivalenceEquals
           {A : Type} (DER1 DER2 : DecidableEquivalence A) : Prop :=
  DER1 c= DER2 /\ DER2 c= DER1.

Notation "D '===' E" := (decidableEquivalenceEquals E D) 
    (no associativity, at level 70) : decidableEquivalence_scope.
    (* \equiv *)

(* equality *)
(* eq on any type is an equivalence *)

Definition eqEquivalence {A : Type} :
  (Equivalence A (@eq A)) :=
  Definition_of_equivalence _ _
    (@eq_refl A) (@eq_trans A) (@eq_sym A).

(* eq on any (Fin.t n) is decidable *)

Lemma eqFinDecidable (n : nat) : isDecidable (@eq (Fin.t n)).
Proof.
  unfold isDecidable; apply t_eqdec.
Qed.

(* so equality on any Fin.t n is a decidable equivalence *)

Definition eqFinDecidableEquivalence {n : nat} :
           DecidableEquivalence (Fin.t n).
Proof.
  exists (@eq (Fin.t n)).
  exact (eqEquivalence, eqFinDecidable n).
Defined.

Notation "'eqFDE'" := eqFinDecidableEquivalence :
                       decidableEquivalence_scope.
         (* \bigtriangleup △ *)

(* eq is the smallest reflexive relation on any type
   so △ ⊆ DER for any decidableEquivalence DER on any Fin.t n *)

Lemma eqSmallestDecidableEquivalence
      {n : nat} (DER : DecidableEquivalence (Fin.t n)) : 
      eqFDE c= DER.
Proof.
  intros x y xEqy.
  rewrite <- xEqy.
  exact (decidableEquivalenceReflexive DER x).
Qed.

(* on (Fin.t 1), any (decidable equivalence) relation is contained
   in eq *)

Lemma eqLargestDecidableEquivalenceFin1
      (DER : DecidableEquivalence (Fin.t 1)) : DER c= eqFDE.
Proof.
  intros x y xRy; exact (fin1IsProp x y).
Qed.

(* on (Fin.t 1), any decidable equivalence is equal to △ *)

Lemma eqOnlyDecidableEquivalenceFin1
      (DER : DecidableEquivalence (Fin.t 1)) : DER === eqFDE.
Proof.
  split.
  - apply eqSmallestDecidableEquivalence.
  - apply eqLargestDecidableEquivalenceFin1.
Qed.


(*******************************************************************)
(* operations on decidableEquivalences                             *)
(*   1) addpair                                                    *)
(*******************************************************************)

(* Given a decidable equivalence relation on a type A and a pair of
   elements x, y, return the smallest equivalence relation 
   containing the given one and the pair (x,y) *)

Definition addpair {A : Type} (x y : A) :
  Relation A -> Relation A :=
    fun R => fun w => fun z =>
       (R w z) \/ ((R w x) /\ (R z y)) \/ ((R w y) /\ (R z x)).

(* addpair preserves decidability *)

Lemma addpairDecidableIsDecidable {A : Type}
      (x y : A) (R : Relation A) :
      (isDecidable R) -> (isDecidable (addpair x y R)).
Proof.
  intro RDec.
  unfold isDecidable. intros w z.
  unfold addpair.
  pose (isRWZ := RDec w z).
  pose (isRWX := RDec w x).
  pose (isRZY := RDec z y).
  pose (isRWY := RDec w y).
  pose (isRZX := RDec z x).
  destruct isRWZ as [RWZ | notRWZ].
  (* "; intuition." does the job but runs too long *)
  - left. left. exact RWZ.
  - destruct isRWX as [RWX | notRWX].
    + destruct isRZY as [RZY | notRZY].
      * left; right; left. exact (conj RWX RZY).
      * { destruct isRWY as [RWY | notRWY].
          - destruct isRZX as [RZX | notRZX].
            + left; right; right. exact (conj RWY RZX).
            + right. intro RapWZ.
              destruct RapWZ as [RWZ | [[_ RZY] | [_ RZX]]]; intuition.
          - right. intro RapWZ.
            destruct RapWZ as [RWZ | [[_ RZY] | [RWY _]]]; intuition.
        }
    + destruct isRWY as [RWY | notRWY].
      * { destruct isRZX as [RZX | notRZX].
          + left; right; right. exact (conj RWY RZX).
          + right. intro RapWZ.
            destruct RapWZ as [RWZ | [[RWX _] | [_ RZX]]]; intuition.
        }
      * right. intro RapWZ.
        destruct RapWZ as [RWZ | [[RWX _] | [RWY _]]]; intuition.
Qed.

(* addpair preserves being an equivalence *)

Lemma addpairReflexiveIsReflexive {A : Type}
           (x y : A) (R : Relation A) :
           (Reflexive _ R) -> (Reflexive _ (addpair x y R)).
Proof. unfold Reflexive, addpair; intuition. Qed.

Lemma addpairSymmetricIsSymmetric {A : Type}
           (x y : A) (R : Relation A) :
           (Symmetric _ R) -> (Symmetric _ (addpair x y R)).
Proof.
  intro RSym. unfold Symmetric in RSym.
  unfold Symmetric. intros w z. unfold addpair.
  intro RapWZ. destruct RapWZ as [RWZ | [[RWX RZY] | [RWY RZX]]].
  - left. exact (RSym w z RWZ).
  - right. right. exact (conj RZY RWX).
  - right. left. exact (conj RZX RWY).
Qed.

Lemma addpairSymmetricTransitiveIsTransitive {A : Type}
           (x y : A) (R : Relation A) :
           (Transitive _ R) -> (Symmetric _ R) ->
           (Transitive _ (addpair x y R)).
Proof.
  intro RTrans. unfold Transitive in RTrans.
  intro RSym. unfold Symmetric in RSym.
  unfold Transitive. intros u v w. unfold addpair.
  intros RapUV RapVW.
  destruct RapUV as [RUV | [[RUX  RVY] | [RUY  RVX]]];
  destruct RapVW as [RVW | [[RVX' RWY] | [RVY' RWX]]].
  - left.         exact (RTrans _ _ _ RUV RVW).
  - right; left.  exact (conj (RTrans _ _ _ RUV RVX') RWY).
  - right; right. exact (conj (RTrans _ _ _ RUV RVY') RWX).
  - right; left.  exact (conj RUX (RTrans _ _ _ (RSym _ _ RVW) RVY)).
  - right; left.  exact (conj RUX RWY).
  - left.         exact (RTrans _ _ _ RUX (RSym _ _ RWX)).
  - right; right. exact (conj RUY (RTrans _ _ _ (RSym _ _ RVW) RVX)).
  - left.         exact (RTrans _ _ _ RUY (RSym _ _ RWY)).
  - right; right. exact (conj RUY RWX).
Qed.

Lemma addpairEquivalenceIsEquivalence {A : Type}
      (x y : A) (R : Relation A) :
      (Equivalence _ R) ->
      (Equivalence _ (addpair x y R)).
Proof.
  intro REq. destruct REq as [RRef RTrans RSym].
  apply Definition_of_equivalence.
  - exact (addpairReflexiveIsReflexive x y R RRef).
  - exact (addpairSymmetricTransitiveIsTransitive x y R RTrans RSym).
  - exact (addpairSymmetricIsSymmetric x y R RSym).
Qed.

Definition addpairDecidableEquivalence {A : Type} :
           A -> A -> DecidableEquivalence A -> DecidableEquivalence A.
Proof.
  intros x y DER.
  destruct DER as [R [E D]].
  exists (addpair x y R).
  exact ((addpairEquivalenceIsEquivalence x y R E) ,
         (addpairDecidableIsDecidable x y R D)).
Defined.

(* elements related before addpair will remain related *)

Lemma addpairIncreasing {A : Type} (x y : A) (R : Relation A) :
        contains A (addpair x y R) R.
Proof.
  unfold contains.
  intros w z wRz.
  unfold addpair.
  left; exact wRz.
Qed.

(* if (addpair x y)  is applied to a reflexive relation, the result
   will relate x and y  *)

Lemma addpairRelatesPair {A : Type} (x y : A) (R : Relation A)
        (RReflexive : Reflexive _ R) : (addpair x y R) x y.
Proof.
  unfold addpair.
  right. left. split.
  - exact (RReflexive x).
  - exact (RReflexive y).
Qed.

(* given a relation R1, an equivalence relation R2, and elements 
   x, y, if R2 contains R1 and relates x and y, then it also contains
   (addpair x y R1) *)

Lemma addpairSmallest {A : Type} (x y : A) (R1 R2 : Relation A)
      (R2Eq : Equivalence _ R2) :
      (contains A R2 R1) -> (R2 x y) -> 
      (contains A R2 (addpair x y R1)).
Proof.
  intros R1subR2 xR2y.
  unfold contains.
  intros w z.
  unfold addpair.
  unfold contains in R1subR2.
  destruct R2Eq as [R2Reflexive R2Transitive R2Symmetric].
  intro wAddPz.
  destruct wAddPz as [wR1z |[ wR1x_zR1y | wR1y_zR1x]].
  - exact (R1subR2 w z wR1z).
  - destruct wR1x_zR1y as [wR1x zR1y].
    apply R1subR2 in wR1x as wR2x.
    apply R1subR2 in zR1y as zR2y.
    apply (R2Transitive w x z wR2x).
    apply (R2Transitive x y z xR2y).
    apply (R2Symmetric _ _ zR2y).
  - destruct wR1y_zR1x as [wR1y zR1x].
    apply R1subR2 in wR1y as wR2y.
    apply R1subR2 in zR1x as zR2x.
    apply R2Symmetric.
    apply (R2Transitive z x w zR2x).
    apply (R2Transitive x y w xR2y).
    apply (R2Symmetric _ _ wR2y).
Qed.


(*******************************************************************)
(* operations on decidable Equivalences                            *)
(*   2) pullback (inverse image)                                   *)
(*******************************************************************)

(* given a map f : A -> B and a relation on B, pull it back along f
   to a relation on A *)

Definition pullbackRelation {A B : Type} (f : A -> B) :
  Relation B -> Relation A :=
  fun R => fun x => fun y => R (f x) (f y).

(* pullback preserves decidability *)

Definition pullbackDecidableIsDecidable {A B : Type}
  (f : A -> B) (R : Relation B) :
  isDecidable R -> isDecidable (pullbackRelation f R) :=
  fun RDec => fun x => fun y => RDec (f x) (f y).

(* pullback preserves being an equivalence *)

Definition pullbackReflexiveIsReflexive {A B : Type}
  (f : A -> B) (R : Relation B) :
  (Reflexive B R) -> Reflexive A (pullbackRelation f R) :=
  fun RRef => fun x => RRef (f x).

Definition pullbackSymmetricIsSymmetric {A B : Type}
  (f : A -> B) (R : Relation B) :
  (Symmetric B R) -> Symmetric A (pullbackRelation f R) :=
  fun RSym => fun x => fun y => RSym (f x) (f y).

Definition pullbackTransitiveIsTransitive {A B : Type}
  (f : A -> B) (R : Relation B) :
  (Transitive B R) -> Transitive A (pullbackRelation f R) :=
  fun RTrans => fun x => fun y => fun z => RTrans (f x) (f y) (f z).

Definition pullbackEquivalenceIsEquivalence {A B : Type}
  (f : A -> B) (R : Relation B) :
  (Equivalence B R) -> Equivalence A (pullbackRelation f R).
Proof.
  intro REq. destruct REq as [RRef RTrans RSym].
  apply Definition_of_equivalence.
  - exact (pullbackReflexiveIsReflexive f R RRef).
  - exact (pullbackTransitiveIsTransitive f R RTrans).
  - exact (pullbackSymmetricIsSymmetric f R RSym).
Defined.

Definition pullbackDecidableEquivalence {A B : Type} :
           (A -> B) -> DecidableEquivalence B -> DecidableEquivalence A.
Proof.
  intros f [R [E D]].
  exists (pullbackRelation f R).
  exact ((pullbackEquivalenceIsEquivalence f R E) ,
         (pullbackDecidableIsDecidable f R D)).
Defined.

(*******************************************************************)
(* operations on sharing relations                                 *)
(*   3) addSingle                                                  *)
(*******************************************************************)

(* build a decidable equivalence on (Fin.t (S n)) from a given one
   on (Fin.t n) determining the relation on the n elements 
   FS F1, ..., FS^n F1, where F1 is related only to itself.        *)

Definition addSingle {n : nat} (R : Relation (Fin.t n)) : 
           Relation (Fin.t (S n)) :=
fun x => fun y => 
  match x, y with  
  | F1 , F1     => fun _ => True
  | F1 , (FS _) => fun _ => False
  | (FS _), F1  => fun _ => False
  | (FS x'), (FS y') => fun R' => R' x' y'
  end R.

(* addSingle preserves decidability *)

Definition addSingleDecidableIsDecidable {n : nat} 
           (R : Relation (Fin.t n)) (rDec : isDecidable R) : 
           isDecidable (addSingle R).
Proof.
  unfold isDecidable.
  intros x y.
  apply (Fin.caseS' x); apply (Fin.caseS' y); compute.
  - (* F1 F1 *) left. exact I.
  - (* F1 FS *) right. trivial.
  - (* FS F1 *) right. trivial.
  - (* FS FS *) intros y' x'. exact (rDec x' y').
Defined.

(* addSingle preserves being an equivalence *)

Definition addSingleReflexiveIsReflexive {n : nat} (R : Relation (Fin.t n)) :
           Reflexive _ R -> Reflexive _ (addSingle R).
Proof.
  intro rRef.
  unfold Reflexive.
  intro x.
  apply (Fin.caseS' x); compute; trivial.
Defined.

Definition addSingleSymmetircIsSymmetric {n : nat} (R : Relation (Fin.t n)) :
           Symmetric _ R -> Symmetric _ (addSingle R).
Proof.
  intro rSym.
  unfold Symmetric. intros x y.
  apply (Fin.caseS' x); apply (Fin.caseS' y);
  compute; trivial.
  intros y' x'.
  exact (rSym x' y').
Defined.

Definition addSingleTransitiveIsTransitive {n : nat} 
           (R : Relation (Fin.t n)) :
           Transitive _ R -> Transitive _ (addSingle R).
Proof.
  unfold Transitive.
  intros rTrans x y z.
  apply (Fin.caseS' x); apply (Fin.caseS' y); 
  apply (Fin.caseS' z); compute; trivial.
  - intros y' x' f.  apply False_ind.
  - intros z' y' x' rXY rYZ. exact (rTrans _ _ _ rXY rYZ).
Defined.

Definition addSingleEquivalenceIsEquivalence {n : nat}
           (R : Relation (Fin.t n)) :
           (Equivalence _ R) -> Equivalence _ (addSingle R).
Proof.
  intro REq. destruct REq as [RRef RTrans RSym].
  apply Definition_of_equivalence.
  - exact (addSingleReflexiveIsReflexive R RRef).
  - exact (addSingleTransitiveIsTransitive R RTrans).
  - exact (addSingleSymmetircIsSymmetric R RSym).
Defined.

Definition addSingleDecidableEquivalence {n : nat} :
           DecidableEquivalence (Fin.t n) ->
           DecidableEquivalence (Fin.t (S n)).
Proof.
  intros [R [E D]].
  exists (addSingle R).
  exact ((addSingleEquivalenceIsEquivalence R E) ,
         (addSingleDecidableIsDecidable R D)).
Defined.

(* addSingle R relates x and y iff both are F1 or come
   from elements related by R  *)

Lemma addSingleCases {n : nat} (R : Relation (Fin.t n))
      (x y : Fin.t (S n)) : (addSingle R x y) ->
      ((x = F1) * (y = F1)) + 
      { x' : Fin.t n & 
      { y' : Fin.t n &  R x' y' * (x = FS x') * (y = FS y') }}.
Proof.
  apply (Fin.caseS' x); apply (Fin.caseS' y).
  - left. split;reflexivity.
  - intros y' impossible. destruct impossible.
  - intros x' impossible. destruct impossible.
  - intros y' x' x'Ry'. compute in x'Ry'.
    right. exists x'. exists y'. split. split.
    + exact x'Ry'.
    + reflexivity.
    + reflexivity.
Qed.


