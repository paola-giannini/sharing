(***************************************************************************
 * Tracing sharing in an imperative pure calculus: sharing relations
          
               Paola Giannini and Tim Richter
 *  
 ***************************************************************************)

Require Import Fin.
Require Import Vector.
Require Import Relations_1.
Require Import Atom.
Require Import Decidable.

Open Scope type_scope. (* to be able to use _ * _ for 
                          the cartesian product of types *)

(* decidability of a relation *)

Definition isDec {A : Type} (R : Relation A) : Type :=
  forall (x y : A), {R x y} + {~ (R x y)}.

(* the type of decidable equivalence relations on a given type *)

Definition Dec_Equivalence (A : Type) : Type :=
  @sigT (Relation A) (fun R => Equivalence _ R * isDec R).

(* We define the type of sharing relations on a (length n)-
   vector l of variables of type atom as the type of decidable
   equivalence relations on the finite set Fin.t (n + 1).

   Here we consider the n elements 1,...,n (i.e. FS (F1),...,
   FS (FS ... (F1)...) (n applications of FS)) as indexing the
   entries of the vector l, and F1 as an index for an additional
   (pseudo) variable (res).

Definition shRel {A : Type} {n : nat} : (Vector.t A n) -> Type :=
  fun l => Dec_Equivalence (Fin.t (S n)).

   Or, maybe better, right away as a type family on lists of 
   atoms:
*)

Definition shRel (l : list atom) : Type :=
  Dec_Equivalence (Fin.t (S (length l))).

(* We can take "Vector.of_list" for vector_from_list. *) 

Definition vector_from_list :
  forall (l: list atom), Vector.t atom (length l) :=
  of_list.

(* the eq relation on any type is an equivalence *)

Definition eq_Reflexive {A : Type} :
  (Reflexive A (@eq A)) := @eq_refl A.

Definition eq_Symmetric {A : Type} :
  (Symmetric A (@eq A)) := @eq_sym A.

Definition eq_Transitive {A : Type} :
  (Transitive A (@eq A)) := @eq_trans A.

Definition eq_Equivalence {A : Type} :
  (Equivalence A (@eq A)) :=
  Definition_of_equivalence _ _
    eq_Reflexive eq_Transitive eq_Symmetric.

(* the eq relation on any (Fin.t n) is decidable *)

Lemma eq_fin_dec (n : nat) : isDec (@eq (Fin.t n)).
Proof.
  unfold isDec.
  intros x y.
  induction n.
  - inversion x.
  - apply (Fin.caseS' x); apply (Fin.caseS' y).
    + (* case F1 F1 *) left. reflexivity.  
    + (* case F1 FS *) right. discriminate.

    + (* case FS F1 *) right. discriminate.
    + (* case (FS x) (FS y) *)
      intros y' x'. destruct (IHn x' y') as [X'eqY' | X'noteqY'].
      * left. rewrite X'eqY'. reflexivity.
      * right. 
        intro FSX'eqFSY'.
        apply FS_inj in FSX'eqFSY' as X'eqY'.
        exact (X'noteqY' X'eqY').
Qed.

Definition eq_Fin_Dec_Equivalence {n : nat} : Dec_Equivalence (Fin.t n).
Proof.
  exists (@eq (Fin.t n)).
  exact (eq_Equivalence, eq_fin_dec n).
Defined.

(* the identity sharing relation *)

Definition id_shRel (l : list atom) : shRel l := 
            eq_Fin_Dec_Equivalence.

Open Scope list_scope. (* for list notation (_::_) *)

(* Index lookup function: given an atom x and a list l, return
   the the first index of l holding x (or None if x is not in l).
*) 

Fixpoint firstIndexOrNone (x : atom) (l : list atom) :
  option (Fin.t (length l)) :=
  match l with
  | List.nil => None
  | (y::ys)  => if (eq_atom_dec x y)
               then Some F1
               else match (firstIndexOrNone x ys) with
               | None   => None
               | Some i => Some (FS i)
               end
  end.

(* Variant returning the successor of the first index holding
   x if x occurs or F1. I.a.w., result is the first index of x
   in the (pseudo) list (res::l). Since we do not consider res
   an atom, we can take the result F1 to signal lookup failure,
   so we don't need option. 
*)

Definition firstIndexOrF1 (x : atom) (l : list atom) :
  Fin.t (S (length l)) :=
  match (firstIndexOrNone x l) with
  | None   => F1
  | Some i => FS i
  end.

(* Given a decidable equivalence relation on a type
   and a pair of elements x, y, return the smallest
   equivalence relation containing the old one and the pair (x,y) 
*)

Definition addpair {A : Type} (x y : A) :
  Relation A -> Relation A :=
    fun R => fun w => fun z =>
       (R w z) \/ ((R w x) /\ (R z y)) \/ ((R w y) /\ (R z x)). 

Lemma addpair_Dec_is_Dec {A : Type}
      (x y : A) (R : Relation A) :
      (isDec R) -> (isDec (addpair x y R)).
Proof.
  intro RDec.
  unfold isDec. intros w z.
  unfold addpair.
  pose (isRWZ := RDec w z).
  pose (isRWX := RDec w x).
  pose (isRZY := RDec z y).
  pose (isRWY := RDec w y).
  pose (isRZX := RDec z x).
  destruct isRWZ as [RWZ | notRWZ].
  - left. left. exact RWZ.
  - destruct isRWX as [RWX | notRWX].
    + destruct isRZY as [RZY | notRZY].
      * left; right; left. exact (conj RWX RZY).
      * { destruct isRWY as [RWY | notRWY].
          - destruct isRZX as [RZX | notRZX].
            + left; right; right. exact (conj RWY RZX).
            + right. intro RapWZ.
              destruct RapWZ as [RWZ | [[_ RZY] | [_ RZX]]].
              * exact (notRWZ RWZ).
              * exact (notRZY RZY).
              * exact (notRZX RZX).
          - right. intro RapWZ.
            destruct RapWZ as [RWZ | [[_ RZY] | [RWY _]]].
            + exact (notRWZ RWZ).
            + exact (notRZY RZY).
            + exact (notRWY RWY).
        }
    + destruct isRWY as [RWY | notRWY].
      * { destruct isRZX as [RZX | notRZX].
          + left; right; right. exact (conj RWY RZX).
          + right. intro RapWZ.
            destruct RapWZ as [RWZ | [[RWX _] | [_ RZX]]].
            - exact (notRWZ RWZ).
            - exact (notRWX RWX).
            - exact (notRZX RZX).
        }
      * { right. intro RapWZ.
          destruct RapWZ as [RWZ | [[RWX _] | [RWY _]]].
          - exact (notRWZ RWZ).
          - exact (notRWX RWX).
          - exact (notRWY RWY).
        }
Qed.

Lemma addpair_Ref_is_Ref {A : Type}
           (x y : A) (R : Relation A) :
           (Reflexive _ R) -> (Reflexive _ (addpair x y R)).
Proof.
  intro RRef. unfold Reflexive in RRef.
  unfold Reflexive.
  intro z. unfold addpair.
  left. exact (RRef z).
Qed.

Lemma addpair_Sym_is_Sym {A : Type}
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

Lemma addpair_SymTrans_is_Trans {A : Type}
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

Lemma addpair_Equivalence_is_Equivalence {A : Type}
      (x y : A) (R : Relation A) :
      (Equivalence _ R) ->
      (Equivalence _ (addpair x y R)).
Proof.
  intro REq. destruct REq as [RRef RTrans RSym].
  apply Definition_of_equivalence.
  - exact (addpair_Ref_is_Ref x y R RRef).
  - exact (addpair_SymTrans_is_Trans x y R RTrans RSym).
  - exact (addpair_Sym_is_Sym x y R RSym).
Qed.

Definition addpair_Dec_Equivalence {A : Type}
           (x y : A) (DER : Dec_Equivalence A) : Dec_Equivalence A.
Proof.
  destruct DER as [R [E D]]. 
  exists (addpair x y R).
  exact ((addpair_Equivalence_is_Equivalence x y R E) ,
         (addpair_Dec_is_Dec x y R D)).
Defined.

(* For use in add_eq_res, firstIndexOrF1 is convenient:
   if x is not found in l, the sharing relation is not altered
   (proof needed?).
*)

Definition add_eq_res {l : list atom} (shR : shRel l) (x : atom) :
  shRel l := addpair_Dec_Equivalence F1 (firstIndexOrF1 x l) shR.

(* addpair can also be used to get add_eq_X *)

Fixpoint add_eq_X {l : list atom}
           (shR: shRel l) (x: atom) (ys: list atom) : shRel l :=
  let ix := firstIndexOrF1 x l in
  match ix with
  |  F1     => shR (* if x not in l, don't change the relation *)
  | (FS _)  => 
    match ys with
    | List.nil => shR
    | (y::ys') =>
      let iy := firstIndexOrF1 y l in
      let recCall := add_eq_X shR x ys' in
      match iy with
      | F1     => recCall
      | (FS _) => addpair_Dec_Equivalence ix iy recCall
      end
    end
  end.

(* given a map f : A -> B and a decidable equivalence
   relation on B, pull it back along f to a decidable
   equivalence relation on A
*)

Definition pullback_Relation {A B : Type} (f : A -> B) :
  Relation B -> Relation A :=
  fun R => fun x => fun y => R (f x) (f y).

Definition pullback_Dec_is_Dec {A B : Type}
  (f : A -> B) (R : Relation B) :
  isDec R -> isDec (pullback_Relation f R) :=
  fun RDec => fun x => fun y => RDec (f x) (f y).

Definition pullback_Ref_is_Ref {A B : Type}
  (f : A -> B) (R : Relation B) :
  (Reflexive B R) -> Reflexive A (pullback_Relation f R) :=
  fun RRef => fun x => RRef (f x).

Definition pullback_Sym_is_Sym {A B : Type}
  (f : A -> B) (R : Relation B) :
  (Symmetric B R) -> Symmetric A (pullback_Relation f R) :=
  fun RSym => fun x => fun y => RSym (f x) (f y).

Definition pullback_Trans_is_Trans {A B : Type}
  (f : A -> B) (R : Relation B) :
  (Transitive B R) -> Transitive A (pullback_Relation f R) :=
  fun RTrans => fun x => fun y => fun z => RTrans (f x) (f y) (f z).

Definition pullback_Equivalence_is_Equivalence {A B : Type}
  (f : A -> B) (R : Relation B) :
  (Equivalence B R) -> Equivalence A (pullback_Relation f R).
Proof.
  intro REq. destruct REq as [RRef RTrans RSym].
  apply Definition_of_equivalence.
  - exact (pullback_Ref_is_Ref f R RRef).
  - exact (pullback_Trans_is_Trans f R RTrans).
  - exact (pullback_Sym_is_Sym f R RSym).
Defined.

Definition pullback_Dec_Equivalence {A B : Type}
           (f : A -> B) (DER : Dec_Equivalence B) : Dec_Equivalence A.
Proof.
  destruct DER as [R [E D]]. 
  exists (pullback_Relation f R).
  exact ((pullback_Equivalence_is_Equivalence f R E) ,
         (pullback_Dec_is_Dec f R D)).
Defined.

(* build a decidable equivalence on (Fin.t (S n)) from
   a given one on (Fin.t n) determining the relation on 
   the n elements FS F1, ..., FS^n and where F1 is unrelated
   to any element but itself.
 *)

Definition addSingle {n : nat} (R : Relation (Fin.t n)) : 
             Relation (Fin.t (S n)) :=
fun x => fun y => 
  match x, y with  
  | F1 , F1     => fun _ => True
  | F1 , (FS _) => fun _ => False
  | (FS _), F1  => fun _ => False
  | (FS x'), (FS y') => fun R' => R' x' y'
  end R.

Definition addSingle_Dec_is_Dec {n : nat} 
  (R : Relation (Fin.t n)) (rDec : isDec R) : 
  isDec (addSingle R).
Proof.
  unfold isDec.
  intros x y.
  apply (Fin.caseS' x); apply (Fin.caseS' y); compute.
  - (* F1 F1 *) left. exact I.
  - (* F1 FS *) right. trivial.
  - (* FS F1 *) right. trivial.
  - (* FS FS *) intros y' x'. exact (rDec x' y').
Defined.

Definition addSingle_Ref_is_Ref {n : nat} (R : Relation (Fin.t n)) :
  Reflexive _ R -> Reflexive _ (addSingle R).
Proof.
  intro rRef.
  unfold Reflexive.
  intro x.
  apply (Fin.caseS' x); compute; trivial.
Defined.

Definition addSingle_Sym_is_Sym {n : nat} (R : Relation (Fin.t n)) :
  Symmetric _ R -> Symmetric _ (addSingle R).
Proof.
  intro rSym.
  unfold Symmetric. intros x y.
  apply (Fin.caseS' x); apply (Fin.caseS' y);
  compute; trivial.
  intros y' x'.
  exact (rSym x' y').
Defined.

Definition addSingle_Trans_is_Trans {n : nat} (R : Relation (Fin.t n)) :
  Transitive _ R -> Transitive _ (addSingle R).
Proof.
  unfold Transitive.
  intros rTrans x y z.
  apply (Fin.caseS' x); apply (Fin.caseS' y); 
  apply (Fin.caseS' z); compute; trivial.
  - intros y' x' f.  apply False_ind.
  - intros z' y' x' rXY rYZ. exact (rTrans _ _ _ rXY rYZ).
Defined.

Definition addSingle_Equivalence_is_Equivalence {n : nat}
           (R : Relation (Fin.t n)) :
  (Equivalence _ R) -> Equivalence _ (addSingle R).
Proof.
  intro REq. destruct REq as [RRef RTrans RSym].
  apply Definition_of_equivalence.
  - exact (addSingle_Ref_is_Ref R RRef).
  - exact (addSingle_Trans_is_Trans R RTrans).
  - exact (addSingle_Sym_is_Sym R RSym).
Defined.

Definition addSingle_Dec_Equivalence {n : nat}
           (DER : Dec_Equivalence (Fin.t n)) : Dec_Equivalence (Fin.t (S n)).
Proof.
  destruct DER as [R [E D]]. 
  exists (addSingle R).
  exact ((addSingle_Equivalence_is_Equivalence R E) ,
         (addSingle_Dec_is_Dec R D)).
Defined.

(* to make res into a singleton, pull back along FS and
   apply addSingle
*)

Definition rem_res {l : list atom} (shR : shRel l) : shRel l := 
  addSingle_Dec_Equivalence (pullback_Dec_Equivalence FS shR).

(* to restrict to a prefix, pull back along Fin.L (length rest)
*)

Definition restrict_res {l2 : list atom} (l1 : list atom) 
  (shR : shRel (l1 ++ l2)) : shRel l1.
Proof.
  unfold shRel in shR; unfold shRel.
  assert (length (l1 ++ l2) = 
     (length l1 + length l2)%nat) as LL1L2 by apply List.app_length.
  assert (S ( length l1 + length l2) = 
     (S (length l1)) + length l2)%nat as SL1L2 by trivial.
  rewrite LL1L2 in shR.
  rewrite SL1L2 in shR.
  exact (pullback_Dec_Equivalence (Fin.L (length l2)) shR).
Defined.

(* We can also erase a prefix from a list and restrict
   the sharing relation to the rest. To preserve the relations
   of res, we have to pull back along the following map:
*)

Fixpoint gapAboveF1 {n : nat} (m : nat) (x : Fin.t (S n)) :
                  Fin.t (S (m + n)).
Proof.
  apply (Fin.caseS' x (fun _ => Fin.t (S (m + n)))).
  - (* F1 *)  exact F1.
  - (* FS x *)  
    intro x'.
    assert ((m + S n)%nat = S (m + n)) as eq 
      by (apply PeanoNat.Nat.add_succ_r).
    pose (t:= Fin.R m (FS x')).
    rewrite eq in t.
    exact t.
Defined.

Definition restrict_res2 {l2 : list atom} (l1 : list atom) 
  (shR : shRel (l1 ++ l2)) : shRel l2.
Proof.
  unfold shRel in shR; unfold shRel.
  assert (length (l1 ++ l2) = 
     (length l1 + length l2)%nat) as LL1L2 by apply List.app_length.
  rewrite LL1L2 in shR.
  exact (pullback_Dec_Equivalence (gapAboveF1 (length l1)) shR).
Defined.

(* list of all elements in Fin.t n *)

Fixpoint listAllFin (n : nat) : list (Fin.t n) :=
  match n with
  | O      => List.nil
  | (S n') => List.cons F1  (List.map FS (listAllFin n'))
  end.

Fixpoint vectAllFin (n : nat) : Vector.t (Fin.t n) n :=
  match n with
  | O      => nil (Fin.t O)
  | (S n') => cons _ F1 _ (map FS (vectAllFin n'))
  end.

Definition vectAllFS (n : nat) : Vector.t (Fin.t (S n)) n :=
  (map FS (vectAllFin n)).

Fixpoint getFirstOrDefault {n : nat} {A : Type} 
  (P : A -> Prop) (isDecP : forall (a : A), {P a} + {~(P a)})
  (v : Vector.t A n) (default : A) {struct v}: A :=
  match v with
  | nil _         => default
  | cons _ y _ v' => if (isDecP y) 
                     then y 
                     else getFirstOrDefault P isDecP v' default
  end.

Definition get_class_minF1 {n : nat} (DER : Dec_Equivalence (Fin.t (S n))) : 
            Fin.t (S n) :=
  let P      := (projT1 DER) F1 in
  let isDecP := (snd (projT2 DER)) F1 in
  getFirstOrDefault P isDecP (vectAllFS n) F1.

Fixpoint getLastOrDefault {n : nat} {A : Type} 
  (P : A -> Prop) (isDecP : forall (a : A), {P a} + {~(P a)})
  (v : Vector.t A n) (default : A) {struct v}: A :=
  match v with
  | nil _         => default
  | cons _ y _ v' => if (isDecP y) 
                     then getLastOrDefault P isDecP v' y
                     else getLastOrDefault P isDecP v' default
  end.

Definition get_class_maxF1 {n : nat} (DER : Dec_Equivalence (Fin.t (S n))) : 
            Fin.t (S n) :=
  let P      := (projT1 DER) F1 in
  let isDecP := (snd (projT2 DER)) F1 in
  getLastOrDefault P isDecP (vectAllFS n) F1.


(* We construct the sum of two equivalences on Fin.t (S n) 
   by induction on n:
   - n = O : on Fin.t 1 there is no equivalence other then the identity,
             so we return the identity
   - n = (S n') 
      - let M1, M2 (in Fin.t (S (S n'))) be the maxima in the equivalence 
        classes of F1 w.r.t. R1, R2
      - pull back R1, R2 to Fin.t (S n'), add them by recursion and apply 
             addSingle  --> call this relation sum'
      - return addpair (F1 M1) (addpair (F1 M2) (addSingle sum')).
*)

Definition sum_Dec_Equivalence {n : nat} 
  (DER1 DER2 : Dec_Equivalence (Fin.t (S n))) : Dec_Equivalence (Fin.t (S n)).
Proof.
  induction n.
  - exact (eq_Fin_Dec_Equivalence).
  - pose (M1 := get_class_maxF1 DER1).
    pose (M2 := get_class_maxF1 DER2).
    pose (sum' := IHn (pullback_Dec_Equivalence FS DER1) 
                      (pullback_Dec_Equivalence FS DER2)).
     exact (addpair_Dec_Equivalence F1 M1 
          (addpair_Dec_Equivalence F1 M2 
          (addSingle_Dec_Equivalence sum'))).
Defined.

Definition add_shr {l : list atom} (shR1 shR2 : shRel l) : shRel l :=
  sum_Dec_Equivalence shR1 shR2.

Fixpoint filter_Dec {A : Type} (P : A -> Prop) 
            (pDec : forall x : A,  {P x} + {~(P x)}) 
            (ys : list A) : list A :=
     match ys with
     | List.nil => List.nil
     | List.cons y ys' => let recCall := filter_Dec P pDec ys' in 
                          if pDec y 
                          then List.cons y recCall
                          else recCall 
     end.


Fixpoint existsL {A : Type} (P : A -> Prop)
                      (ys : list A) : Prop :=
  match ys with
  | List.nil         => False
  | List.cons y ys'  => (P y) \/ existsL P ys'
  end.


Definition existsL_Dec {A : Type} (P : A -> Prop) 
               (pDec : forall x : A,  {P x} + {~(P x)})
               (ys : list A): {existsL P ys} + {~ (existsL P ys)}.
Proof.
  induction ys.
  - right. compute. trivial.
  - induction (pDec a) as [Pa | notPa].
    + left. compute. left. exact Pa.
    + induction (IHys) as [exPys | notexPys].
      * left. compute. right. exact exPys.
      * { right. intro exPays.
          induction exPays as [Pa | exPys].
          - exact (notPa Pa).
          - exact (notexPys exPys).
        }
Defined.

Definition not_Dec_Dec {A : Prop} (aDec : {A} + {~A}) :
              {~ A} + {~ ~ A} :=
  match aDec with
  | left a     => right (fun f => f a)
  | right na   => left na
  end.

Definition capsule {l : list atom} (sr : shRel l) : Prop :=
  let P := fun x => projT1 sr F1 (FS x) in
  ~ (existsL P (listAllFin (length l))).

Definition capsule_Dec {l : list atom} (sr : shRel l) :
           {capsule sr} + {~ (capsule sr)}  :=
           let P    := fun x => projT1 sr F1 (FS x) in
           let pDec := fun x => (snd (projT2 sr)) F1 (FS x) in
           not_Dec_Dec (existsL_Dec P pDec (listAllFin (length l))). 

Definition eq_res {l : list atom} (sr : shRel l) : list atom :=
  let P := fun x => projT1 sr F1 (FS x) in
  let pDec := fun x => (snd (projT2 sr)) F1 (FS x) in
  let idxs := filter_Dec P pDec (listAllFin (length l)) in
  List.map (nth (vector_from_list l)) idxs.

