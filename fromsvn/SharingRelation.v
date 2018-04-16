Require Import Fin.
Require Import Vector.
Require Import Relations_1.
Require Import Atom.
Require Import Decidable.
Require Import DecidableEquivalences.


(*******************************************************************)
(* type of sharing relations                                       *)
(*******************************************************************)

(* We define the type of sharing relations on a list l of variables
   of type atom as the type of decidable equivalence relations on
   the finite set Fin.t ((length l) + 1).

   We consider the n elements 1,...,n (i.e. FS (F1),...,
   FS (FS ... (F1)...) (n applications of FS)) as indexing the
   entries of the list l, and F1 as the index for an additional
   (pseudo) variable (res). *)

Definition shRel (l : list atom) : Type :=
  DecidableEquivalence (Fin.t (S (length l))).

(* projections of components - may be useful in poofs *)

Definition relationOfShRel {l : list atom} (sr : shRel l) :
           Relation (Fin.t (S (length l))) :=
  relationOfDecidableEquivalence sr.

Definition shRelReflexive {l : list atom} (sr : shRel l) : 
           Reflexive _ (relationOfShRel sr) :=
  decidableEquivalenceReflexive sr.

Definition shRelTransitive {l : list atom} (sr : shRel l) : 
           Transitive _ (relationOfShRel sr) :=
  decidableEquivalenceTransitive sr.

Definition shRelSymmetric {l : list atom} (sr : shRel l) : 
           Symmetric _ (relationOfShRel sr) :=
  decidableEquivalenceSymmetric sr.

(*
(*******************************************************************)
(* containment and equality of sharing Relations                   *)
(*******************************************************************)

Definition containedShR {l : list atom} (sr1 sr2 : shRel l) : Prop :=
  contains _ (projT1 sr2) (projT1 sr1).

Definition equalShR {l : list atom} (sr1 sr2 : shRel l) : Prop :=
  containedShR sr1 sr2 /\ containedShR sr2 sr1.
*)


(*******************************************************************)
(* identity sharing relation                                       *)
(*******************************************************************)

(* the identity sharing relation *)

Definition id_shRel (l : list atom) : shRel l := 
            eqFinDecidableEquivalence.


Open Scope decidableEquivalence_scope.

(*
Parameter l : list atom.
Parameter shR : shRel l.
Check (shR ⊆ Δ).
*)

(*******************************************************************)
(* helper functions for index lookup                               *)
(*******************************************************************)

Open Scope list_scope. (* for list notation (_::_) *)

(* Given an atom x and a list l, return the the first index of l
   holding x (or None if x is not in l). *) 

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

(* Variant returning the successor of the first index holding x if
   x occurs in l, and F1 otherwise. I.a.w., result is the first index
   of x in the (pseudo) list (res::l). Since we do not consider res
   an atom, we can take the result F1 to signal lookup failure. *)

Definition firstIndexOrF1 (x : atom) (l : list atom) :
  Fin.t (S (length l)) :=
  match (firstIndexOrNone x l) with
  | None   => F1
  | Some i => FS i
  end.




(* Given a sharing relation shR and an atom x, return the smallest
   sharing relation containing shR and connecting x with the result,
   i.e. contains the pair (F1,index(x)).

   For use in add_eq_res, firstIndexOrF1 is convenient:
   if x is not found in l, the sharing relation is not altered.
*)

Definition add_eq_res {l : list atom} (shR : shRel l) (x : atom) :
  shRel l := addpairDecidableEquivalence F1 (firstIndexOrF1 x l) shR.

(* Given a sharing relation on a list l, an atom x and another list ys,
   build the smallest sharing relation containing l and also connecting
   x (if it is in l) to any element of ys (that are in l) *)

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
      | F1     => recCall  (* if y not in l, don't change the relation *)
      | (FS _) => addpairDecidableEquivalence ix iy recCall
      end
    end
  end.


(* to make res into a singleton, pull back along FS and apply 
   addSingle *)

Definition rem_res {l : list atom} (shR : shRel l) : shRel l := 
           addSingleDecidableEquivalence 
               (pullbackDecidableEquivalence FS shR).

(* to restrict to a prefix, pull back along Fin.L (length rest) *)

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
  exact (pullbackDecidableEquivalence (Fin.L (length l2)) shR).
Defined.

(* We can also erase a prefix from a list and restrict the sharing
   relation to the rest. To preserve the relations of res, we have 
   to pull back along the following map: *)

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
  exact (pullbackDecidableEquivalence (gapAboveF1 (length l1)) shR).
Defined.

(* list of all elements in Fin.t n *)

Fixpoint listAllFin (n : nat) : list (Fin.t n) :=
  match n with
  | O      => List.nil
  | (S n') => List.cons F1  (List.map FS (listAllFin n'))
  end.

Fixpoint vectAllFin (n : nat) : Vector.t (Fin.t n) n :=
  match n with
  | O      => nil
  | (S n') => cons F1 (map FS (vectAllFin n'))
  end.

Definition vectAllFS (n : nat) : Vector.t (Fin.t (S n)) n :=
  (map FS (vectAllFin n)).

(* for a decidable property P of elements of a vector and some
   default satisfying P, return the element with the largest 
   index satisfying P or the default when no element of the 
   vector satisfies P. In both cases, the result satisfies P,
   so return the proof also *)

Fixpoint getLastOrDefault' {n : nat} {A : Type} (P : A -> Prop)
         (isDecP : forall (a : A), {P a} + {~(P a)})
         (v : Vector.t A n) (default : A) (Pd : P default) 
         {struct v}: { x : A & P x } :=
  match v with
  | nil        => existT _ default Pd
  | cons y v'  => 
    match (isDecP y) with
    | left Py  => getLastOrDefault' P isDecP v' y Py
    | right _  => getLastOrDefault' P isDecP v' default Pd
    end
  end.

(* project out the element *)

Definition getLastOrDefault {n : nat} {A : Type} (P : A -> Prop)
           (isDecP : forall (a : A), {P a} + {~(P a)})
           (v : Vector.t A n) (default : A) (Pd : P default) : A :=
  projT1 (getLastOrDefault' P isDecP v default Pd).

(* and the proof *)

Definition getLastOrDefaultP {n : nat} {A : Type} (P : A -> Prop)
           (isDecP : forall (a : A), {P a} + {~(P a)})
           (v : Vector.t A n) (default : A) (Pd : P default) : 
           P (getLastOrDefault P isDecP v default Pd) :=
  projT2 (getLastOrDefault' P isDecP v default Pd).

(* Given a decidable equivalence DER on some Fin.t (S n), return the
   largest element that is related to F1 w.r.t. DER  *)

(* first along with a proof that it is related to F1 *)

Definition classMaxF1' {n : nat} 
           (DER : DecidableEquivalence (Fin.t (S n))) : 
           { x : Fin.t (S n) & (projT1 DER) F1 x } :=
  let P      := (projT1 DER) F1 in
  let isDecP := (snd (projT2 DER)) F1 in
  let RReflexiv := match (fst (projT2 DER)) with
                   | Definition_of_equivalence _ _ r _ _ => r
                   end in
  let PF1    := RReflexiv F1 in
  getLastOrDefault' P isDecP (vectAllFS n) F1 PF1.

(* now project out the element *)

Definition classMaxF1 {n : nat} 
           (DER : DecidableEquivalence (Fin.t (S n))) : 
           Fin.t (S n) :=
  projT1 (classMaxF1' DER).

(* and the proof that it is related to F1 *)

Definition classMaxF1_related {n : nat} 
           (DER : DecidableEquivalence (Fin.t (S n))) : 
           (projT1 DER) F1 (classMaxF1 DER) :=
  projT2 (classMaxF1' DER).


(* Construct the sum of two equivalences R1, R2 on Fin.t (S n) 
   by induction on n:
   - n = O : on Fin.t 1 there is no equivalence other then the 
             identity, so we return the identity
   - n = (S n') 
      - let M1, M2 (in Fin.t (S (S n'))) be the maxima in the 
        equivalence classes of F1 w.r.t. R1, R2
      - pull back R1, R2 to Fin.t (S n'), add them by recursion 
        and apply addSingle  --> call this relation sum'
      - return addpair (F1 M1) (addpair (F1 M2) (addSingle sum')). *)

Definition sum_Dec_Equivalence {n : nat} 
           (DER1 DER2 : DecidableEquivalence (Fin.t (S n))) : 
           DecidableEquivalence (Fin.t (S n)).
Proof.
  induction n.
  - exact (eqFinDecidableEquivalence).
  - pose (M1 := classMaxF1 DER1).
    pose (M2 := classMaxF1 DER2).
    pose (sum' := IHn (pullbackDecidableEquivalence FS DER1) 
                      (pullbackDecidableEquivalence FS DER2)).
    exact (addpairDecidableEquivalence F1 M1 
          (addpairDecidableEquivalence F1 M2 
          (addSingleDecidableEquivalence sum'))).
Defined.

Definition add_shr {l : list atom} 
           (shR1 shR2 : shRel l) : shRel l :=
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
           (ys : list A): 
           {existsL P ys} + {~ (existsL P ys)}.
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
  let P    := fun x => projT1 sr F1 (FS x) in
  let pDec := fun x => (snd (projT2 sr)) F1 (FS x) in
  let idxs := filter_Dec P pDec (listAllFin (length l)) in
  List.map (nth (Vector.of_list l)) idxs.

