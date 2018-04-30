Require Import Decidable.
Require Import Arith.
Require Import NatMisc.
Require Import DecidableEquivalences.
Require Import Fin.
Require Import Vector.
Require Import FinVectorMisc.
Import VectorNotations.
From Equations Require Import Equations.
Set Equations Transparent.
(*Unset Equations WithK.*)

(** Equivalence relations on {0,1,...,n-1} **)

(*
   To build a type of all equivalence relations on {0,1,...,n-1}, just
   describe the process of putting elements into their classes one by one:

   - start with an empty list of classes
   - assuming {0,1,...,i-1} have been put into classes already, either
     + the element i is not related to any of the lower elements,
       thus forming a new class, or
     + i belongs to one of the existing classes.

   This translates into an inductive type family indexed by n and
   the number of classes: 
*)

Inductive ER : nat -> nat -> Type :=
  | EREmpty : ER O O
  | ERNew   : forall {n c : nat},            ER n c -> ER (S n) (S c)
  | ERPut   : forall {n c : nat}, Fin.t c -> ER n c -> ER (S n)  c.

Notation "#"        := EREmpty.
Notation "e '<*'"   := (ERNew e) (at level 70).
Notation "e '<<' x" := (ERPut x e) (at level 69, left associativity).

(* unfortunately, <* and <<  cannot be used in patterns *)

Notation F2 := (FS F1).  Notation F3 := (FS F2). Notation F4 := (FS F3).
Notation F5 := (FS F4).  Notation F6 := (FS F5). Notation F7 := (FS F6).
Notation F8 := (FS F7).  Notation F9 := (FS F8).

(* the type of all equivalence relations on {0,...,n-1} becomes: *)

Definition EqR (n : nat) : Type := { c : nat & ER n c }.

(* ... *)

Notation "'{|' x ';' p '|}'" := (existT _ x p).

Definition toEqr {n c : nat} (e : ER n c) : EqR n := {| c ; e |}.

(** special equivalences **)

(* the identity relation *)

Equations idRel {n : nat} : ER n n :=
idRel {n:=O}     := EREmpty;
idRel {n:=(S m)} := ERNew idRel.

(* Note: an analogue of Lemma EqRF.idRelStructure is auto-generated
   as idRel_equation_2  *)

(* test computation
Eval compute in (erMap (@idRel 5)).
*)

Definition idEqr {n : nat} : EqR n := {| n ; idRel |}.

(* the all relation *)

Equations allRel {n : nat} : ER (S n) 1 :=
allRel {n:=O}     := ERNew EREmpty;
allRel {n:=(S m)} := ERPut F1 allRel.

Equations allEqr {n : nat} : EqR n := 
allEqr {n:=0}     := {| 0 ; EREmpty |};
allEqr {n:=(S _)} := {| 1 ; allRel  |}.


(** elementary properties of ER **)

(* any element of ER 0 0 is equal to EREmpty *)

Equations er00Empty (e : ER 0 0) : e = # :=
er00Empty # := eq_refl.

(* if ER n c is inhabited, c <= n *)

Equations erCLeN {n c : nat} (e : ER n c) : c <= n :=
erCLeN  EREmpty     := @le_n 0;
erCLeN (ERNew e')   := leNS (erCLeN e');
erCLeN (ERPut t e') := le_S _ _ (erCLeN e').

(* idRel n is the only element of ER n n *)

Equations ernnIdRel {n : nat} (e : ER n n) : e = idRel :=
ernnIdRel {n:=0}      EREmpty     := eq_refl;
ernnIdRel {n:=(S _)} (ERNew e')   := f_equal ERNew (ernnIdRel e');
ernnIdRel {n:=(S _)} (ERPut t e') := False_rect _ (nleSuccDiagL _ (erCLeN e')).

(* any equivalence relation with exactly 1 class is allRel *)

Equations ern1AllRel {n : nat} (e : ER (S n) 1) : e = allRel :=
ern1AllRel {n:=0}      (ERNew EREmpty)     := eq_refl;
ern1AllRel {n:=(S _)}  (ERNew (ERPut t _)) :=! t;
ern1AllRel {n:=(S _)}  (ERPut F1 e1)       := f_equal (ERPut F1) (ern1AllRel e1).

(** elementary properties of Eqr **)

Equations eqr0Id (e : EqR 0) : e = idEqr :=
eqr0Id (existT 0 EREmpty) := eq_refl.


(** erMap **)

(* erMap e is the Vector of length n, with the class of the ith element
   of Fin.t n w.r.t. e at the ith position. I.e., it is the tabulation
   of the map sending an element to its equivalence class. *)

Equations erMap {n c : nat} (e : ER n c) : Vector.t (Fin.t c) n :=
erMap  #           := nil;
erMap (ERNew e')   := shiftin (FL _) (map FU (erMap e'));
erMap (ERPut t e') := shiftin t              (erMap e').

Notation "e '@@' t" := (Vector.nth (erMap e) t) (at level 5).

(* test computations
Eval compute in (erMap (# <* << F1 <* << F2 << F1)).
(* representation of [[1,2,5],[3,4,9],[6,8],[7]] *)
Eval compute in
    (erMap (# <* << F1 <* << F2 << F1 <* <* << F3 << F2)).
(*  [[1],[2,4],[3,5,6]] *)
Eval compute in (erMap (# <* <* <* << F2 << F3 << F3)).
*)

(* computation lemmata for @@ *)

Definition erMapNewLast {n c : nat} (e : ER n c) :
           (ERNew e) @@ (FL n) = FL c.
Proof.
  apply shiftinLast.
Defined.

Definition erMapNewPrevious {n c : nat} (e : ER n c) (t : Fin.t n) :
           (ERNew e) @@ (FU t) = FU (e @@ t).
Proof.
  replace ((ERNew e) @@ (FU t)) with
          (nth (shiftin (FL c) (map FU (erMap e))) (FU t)) 
           by trivial.
  rewrite (shiftinPrevious (FL c) (map FU (erMap e)) t).
  apply nthMapLemma.
Defined.

Definition erMapPutLast {n c : nat} (e : ER n c) (x : Fin.t c) :
           (ERPut x e) @@ (FL n) = x.
Proof.
  apply shiftinLast.
Defined.

Definition erMapPutPrevious {n c : nat} (e : ER n c)
                            (x : Fin.t c) (t : Fin.t n) :
           (ERPut x e) @@ (FU t) = (e @@ t).
Proof.
  replace ((ERPut x e) @@ (FU t)) with
          (nth (shiftin x (erMap e)) (FU t)) 
          by trivial.
  apply (shiftinPrevious x (erMap e) t).
Defined.

(* erMap of idRel is the identity *)

Equations(noind) idRelId {n : nat} (x : Fin.t n) : idRel @@ x = x :=
idRelId {n:=0}     x :=! x;
idRelId {n:=(S _)} x with finFUOrFL x := {
                     | (inl (existT y eq (* x = FU y *))) :=
                       (* idRel @@ x *) (eq_trans
                         (f_equal _ eq)
                       (* idRel @@ (FU y) *) (eq_trans
                         (erMapNewPrevious idRel y)
                       (* FU (idRel @@ y) *) (eq_trans
                         (f_equal FU (idRelId y))
                       (* FU y *)
                         (eq_sym eq))));
                     | (inr eq) (* x = FL _ *) := 
                       (* idRel @@ x *) (eq_trans
                         (f_equal _ eq)
                       (* idRel @@ (FL n') *) (eq_trans
                         (erMapNewLast idRel)
                       (* FL n' *)
                         (eq_sym eq)))}.

(** composition **)

Equations erCompose {n c d: nat} (e1 : ER n c) (e2 : ER c d) : ER n d :=
erCompose {n:=0}      EREmpty       EREmpty       :=  EREmpty;
erCompose {n:=(S _)} (ERNew e1')   (ERNew e2')    := (ERNew (erCompose e1' e2'));
erCompose {n:=(S _)} (ERNew e1')   (ERPut t2 e2') := (ERPut t2 (erCompose e1' e2'));
erCompose {n:=(S _)} (ERPut t1 e1') e2            := (ERPut (e2 @@ t1) (erCompose e1' e2)).

(* Lemmata erComposeNN, ~NP and ~P are autogenerated as 
   erCompose_equation_2, ~_3, ~_4  *)

Notation  "e1 '**' e2" := (@erCompose _ _ _ e1 e2) 
                         (at level 60, right associativity).

(* example computation
Eval compute in ((# <* << F1 <* << F2 <* ) ** (# <* <* << F2)).
*)


(* idRel is left and right unit for ** *)

Equations idRelLeft1 {n c : nat} (e : ER n c) : idRel ** e = e :=
idRelLeft1 {n:=0}      EREmpty     :=  eq_refl;
idRelLeft1 {n:=(S _)} (ERNew e')   := (f_equal ERNew (idRelLeft1 e'));
idRelLeft1 {n:=(S _)} (ERPut t e') := (f_equal (ERPut t) (idRelLeft1 e')).

Equations idRelRight1 {n c : nat} (e : ER n c) : e ** idRel = e :=
idRelRight1 {n:=0}      EREmpty     :=  eq_refl;
idRelRight1 {n:=(S _)} (ERNew e')   := (f_equal ERNew (idRelRight1 e'));
idRelRight1 {n:=(S _)} (ERPut t e') :=
             (* (e' << t) ** idRel *) (eq_trans
                (erCompose_equation_4 _ _ _ _ _ _)
             (* (e' ** idRel) << (idRel @@ t) *) (eq_trans
                (f_equal (fun t' => (ERPut t' (e' ** idRel))) (idRelId t (* idRel @@ t = t *)))
             (* (e' ** idRel) << t *)
                (f_equal (ERPut t) (idRelRight1 e' (* e' ** idRel = e' *)))
             (* (e' << t) *) )).

(* postcomposing with allRell maps to allRel *)

Definition allRelRight {n d : nat} (e : ER (S n) (S d)) : e ** allRel = allRel.
Proof.
  apply ern1AllRel.
Defined.

(* erMap of "e1 ** e2" is composition of erMaps *)

Ltac erRewrites0 :=
  try repeat  (rewrite erMapNewPrevious) ||
              (rewrite erMapNewLast)     ||
              (rewrite erMapPutPrevious) ||
              (rewrite erMapPutLast)     || trivial.

Obligation Tactic := program_simpl; erRewrites0.

Equations(noind) erMapCompose {n m l : nat} (e1 : ER n m) (e2 : ER m l) 
                       (x : Fin.t n) :
                       (e1 ** e2) @@ x = e2 @@ (e1 @@ x) :=
erMapCompose {n:=0}     _  _  x                :=! x;
erMapCompose {n:=(S _)} e1 e2 x with finFUOrFL x := {
  erMapCompose {n:=(S _)} (ERNew e1')    (ERNew e2')    x (inl {| y ; eq |}) 
                                        with erMapCompose e1' e2' y := { | IH := _};
  erMapCompose {n:=(S _)} (ERNew e1')    (ERNew e2')    x (inr eq)            := _;
  erMapCompose {n:=(S _)} (ERNew e1')    (ERPut t2 e2') x (inl {| y ; eq|} )  := _;
  erMapCompose {n:=(S _)} (ERNew e1')    (ERPut t2 e2') x (inr eq)            := _;
  erMapCompose {n:=(S _)} (ERPut t1 e1')  e2            x (inl {| y ; eq |})  := _;
  erMapCompose {n:=(S _)} (ERPut t1 e1')  e2            x (inr eq)            := _}.
Next Obligation.
  rewrite IH. trivial.
Defined.

Obligation Tactic := program_simpl.

(* composition is associative *)

Lemma erComposeAssociative {n m l k : nat}
      (e1 : ER n m) (e2 : ER m l) (e3 : ER l k) :
      (e1 ** e2) ** e3 = e1 ** e2 ** e3.
Proof.
  funelim (e1 ** e2).
  - funelim (EREmpty ** e3). trivial.
  - funelim (ERNew (e ** e0) ** e3).
    + repeat (rewrite erCompose_equation_2).
      rewrite H1. trivial.
    + repeat (rewrite erCompose_equation_3).
      rewrite H1. trivial.
  - repeat (rewrite erCompose_equation_4).
    rewrite erCompose_equation_3.
    rewrite H. trivial.
  - repeat (rewrite erCompose_equation_4).
    rewrite H. rewrite erMapCompose. trivial.
Defined.



(** containment **)

Definition erContains {n m l : nat} (f: ER n m) (e: ER n l) : Type :=
           { d : ER m l | f ** d = e }.

Notation "f '[='  e" := (erContains f e) (at level 50).

Definition eqrContains {n : nat} (f e : EqR n) : Type :=
      (projT2 f) [= (projT2 e).

Notation "e 'C='  f" := (eqrContains e f) (at level 50).


(* [= is Reflexive and Transitive *)

Definition erContainsReflexive {n m : nat} (e : ER n m) : e [= e :=
           (exist _ idRel  (idRelRight1 e)).

Definition erContainsTransitive {n c1 c2 c3 : nat}
           (e1 : ER n c1) (e2 : ER n c2) (e3 : ER n c3) :
           (e1 [= e2) -> (e2 [= e3) -> (e1 [= e3).
Proof.
  intros [d1 eq1] [d2 eq2].
  exists (d1 ** d2).
  rewrite <- erComposeAssociative.
  rewrite eq1.
  exact eq2.
Defined.

(* C=  is a partial order (reflexive, transitive and antisymmetric) *)

Definition eqrContainsReflexive {n : nat} (e : EqR n) : e C= e :=
           erContainsReflexive (projT2 e).

Definition eqrContainsTransitive {n : nat} 
           (e1 e2 e3 : EqR n) :
           (e1 C= e2) -> (e2 C= e3) -> (e1 C= e3).
Proof.
  apply erContainsTransitive.
Defined.

Lemma eqrContainsAntiSymmetric {n : nat}
          (e1 e2 : EqR n) :
          (e1 C= e2) -> (e2 C= e1) -> e1 = e2.
Proof.
  destruct e1 as [c1 e1].
  destruct e2 as [c2 e2].
  unfold "C=". simpl.
  intros [d1 eq1] [d2 eq2].
  pose (erCLeN d1) as C2LeC1.
  pose (erCLeN d2) as C1LeC2.
  pose (leAntiSymmetric _ _ (conj C1LeC2 C2LeC1)) as eq.
  destruct eq.
  pose (ernnIdRel d1) as d1Id.
  rewrite d1Id in eq1.
  rewrite (idRelRight1 e1) in eq1.
  rewrite eq1.
  trivial.
Defined.

(* idEqr is minimal for C= *)

Definition idEqrMin {n : nat} (e : EqR n) : idEqr C= e.
Proof.
  destruct e as [d e].
  unfold "C=". simpl.
  exists e.
  apply idRelLeft1.
Defined.

(* allEqr is maximal for C= *)

Equations allEqrMax {n : nat} (e : EqR n) : e C= allEqr :=
allEqrMax {n:=0}     (existT 0 EREmpty)      := eqrContainsReflexive _;
allEqrMax {n:=(S _)} (existT 0 (ERPut t e1)) :=! t;
allEqrMax {n:=(S _)} (existT (S _) e1)       := _.
Next Obligation.
  unfold "C="; simpl.
  exists allRel.
  apply allRelRight.
Defined.

(* we probably need characterisation of [= in terms of erMap: *)

(* the decidable equivalence relation on Fin.t n defined by e : EqR *)

Definition eqrToDecEq {n : nat} (e : EqR n) : DecidableEquivalence (Fin.t n).
Proof.
  destruct e as [c e1].
  apply (pullbackDecidableEquivalence (fun x => e1 @@ x)).
  exact eqFinDecidableEquivalence.
Defined.

Lemma eqrToDecEqPreservesContains {n : nat} (e f : EqR n) 
                                  (p : e C= f) :
                                  (eqrToDecEq e) c= (eqrToDecEq f).
Proof.
  destruct e as [c e], f as [d f].
  unfold "C=","[=" in p; simpl in p. destruct p as [g eq].
  unfold "c=", Relations_1.contains, eqrToDecEq,
         pullbackDecidableEquivalence, pullbackRelation; simpl.
  intros x y eMapEq.
  repeat rewrite <- eq.
  repeat rewrite erMapCompose.
  rewrite eMapEq.
  reflexivity.
Defined.

(* restrict equivalence on n+1 elements to the first n elements *)
Equations eqrShrink {n : nat} (e : EqR (S n)) : EqR n :=
eqrShrink {| _ ; (e' <*)|}   := {| _ ; e' |};
eqrShrink {| _ ; (e' << _)|} := {| _ ; e' |}.

Equations eqrShrinkPreservesContains {n : nat} (e f : EqR (S n))
                                     (p : e C= f) : (eqrShrink e) C= (eqrShrink f) :=
eqrShrinkPreservesContains {| _ ; (e' <*)  |} {| _ ; (f' <*)  |} (exist d eq) := _;
eqrShrinkPreservesContains {| _ ; (e' <*)  |} {| _ ; (f' << t)|} (exist d eq) := _;
eqrShrinkPreservesContains {| _ ; (e' << t)|} {| _ ;  f       |} (exist d eq) := _.
Next Obligation.

(*
Lemma eqrToDecEqReflectsContains {n : nat} (e f : EqR n) 
                                 (p : (eqrToDecEq e) c= (eqrToDecEq f)) :
                                 e C= f.
Proof.
  induction n.
  - rewrite (eqr0Id e). apply idEqrMin.
  - destruct e as [c e], f as [d f].
    unfold "c=", Relations_1.contains, eqrToDecEq,
         pullbackDecidableEquivalence, pullbackRelation in p; simpl in p.
    induction d.
    + apply Fin.case0. exact (f @@ F1).
    +     ... try with Equations...
    unfold "C=","[="; simpl.
  induction n.
  - pose (eqr0Id {| c ; e |}) as eq.
    pose (f_equal projT1 eq).
*)

Equations test1 {n m l : nat} (f : ER (S n) m) ( e : ER n l) 
                (co1 : f [= (e <*)) : { m' : nat & {f' : ER n m' & ((f = (f' <*)) * f' [= e)%type }} :=
test1 _ _ _ := _.
test1 {n:=0}     {m:=0}     {l:=0}     # # _  := (exist _ # eq_refl);
test1 {n:=(S _)} {m:=0}                f _  _ :=! f;
test1 {n:=(S _)}             {l:=0}     _ e  _ :=! e;
test1 {n:=(S _)} {m:=(S _)} {l:=(S _)} f e (exist (ERNew d') eq) := _;
test1 {n:=(S _)} {m:=(S _)} {l:=(S _)} f e (exist (ERPut t d') eq) := _.
Next Obligation.
  admit.
Admitted.
Next Obligation.
  apply False_rect.


Lemma erContainsUnique {n m l : nat} (f: ER n m) (e: ER n l)
         (d1 d2 : f [= e) : d1 = d2.
Proof.
  destruct d1 as [d1 eq1].
  destruct d2 as [d2 eq2].
  destruct eq2.
  destruct eq1.
...?
*)


(* meet *)

Equations eqrMeet (n : nat) (e1 e2 : EqR n) : 
                   { e : EqR n & ( (e C= e1) * (e C= e2) * 
                     forall e' : EqR n,
                        e' C= e1 -> e' C= e2 -> e' C= e)%type } :=
eqrMeet n e1 e2 by rec n lt :=
eqrMeet 0     {| _ ; # |}        {| _ ; # |} := _;
eqrMeet (S _) {| _ ; (e1' <*)|}  {| _ ; (e2' <*)|}
                            with (eqrMeet _ (toEqr e1') (toEqr e2')) := {
                               | {| {| d3 ; e3 |} ; (c1,c2,uni) |} := _};
eqrMeet (S _) (existT _ (ERPut t1 e1'))     (existT _ (ERNew e2'))
                            with (eqrMeet _ (toEqr e1') (toEqr e2')) := {
                               | IH := _};
eqrMeet (S _) (existT _ (ERNew e1'))     (existT _ (ERPut t2 e2'))
                            with (eqrMeet _ (toEqr e1') (toEqr e2')) := {
                               | IH := _};
eqrMeet (S _) (existT _ (ERPut t1 e1'))     (existT _ (ERPut t2 e2'))
                            with (eqrMeet _ (toEqr e1') (toEqr e2')) := {
                               | IH := _}.
Next Obligation.
  exists idEqr. split.
  - split; exact (idEqrMin _).
  - intro e'. cut (e' = idEqr).
    + intros eq _ _. rewrite eq. apply idEqrMin.
    + apply eqr0Id.
Defined.
Next Obligation.
  clear eqrMeet.
  exists {| (S d3) ; (e3 <*) |}. 
  unfold "C=" in *; simpl in *; repeat split.
  + unfold "[=" in c1. destruct c1 as [d eq].
    exists (d <*). rewrite erCompose_equation_2. rewrite eq. reflexivity.
  + unfold "[=" in c2. destruct c2 as [d eq].
    exists (d <*). rewrite erCompose_equation_2. rewrite eq. reflexivity.
  + intros [d e'']; simpl. unfold "[="; intros [d1 eq1] [d2 eq2].
    induction e''.

(* subsets ... 1st attempt *)

Inductive Sub : nat -> Type :=
  | SEmpty : Sub 0
  | SNew   : forall {n : nat}, Sub n -> Sub (S n)
  | SOld   : forall {n : nat}, Sub n -> Sub (S n).

Equations emptySub {n : nat} : Sub n :=
emptySub {n:=0}      := SEmpty;
emptySub {n:=(S n')} := SOld emptySub.

Equations fullSub {n : nat} : Sub n :=
fullSub {n:=0}      := SEmpty;
fullSub {n:=(S n')} := SNew emptySub.

Equations subMeet {n : nat} (s1 s2 : Sub n) : Sub n :=
subMeet SEmpty     _        := SEmpty;
subMeet (SNew t1) (SNew t2) := SNew (subMeet t1 t2);
subMeet (SNew t1) (SOld t2) := SOld (subMeet t1 t2);
subMeet (SOld t1) (SNew t2) := SOld (subMeet t1 t2);
subMeet (SOld t1) (SOld t2) := SOld (subMeet t1 t2).

Equations subJoin {n : nat} (s1 s2 : Sub n) : Sub n :=
subJoin SEmpty     _        := SEmpty;
subJoin (SNew t1) (SNew t2) := SNew (subJoin t1 t2);
subJoin (SNew t1) (SOld t2) := SNew (subJoin t1 t2);
subJoin (SOld t1) (SNew t2) := SNew (subJoin t1 t2);
subJoin (SOld t1) (SOld t2) := SOld (subJoin t1 t2).

Equations(noind) singleSub {n : nat} (x : Fin.t n) : Sub n :=
singleSub {n:=0} x     :=! x;
singleSub {n:=(S _)} x with finFUOrFL x := {
                       | (inl (existT x' _)) := SOld (singleSub x');
                       | (inr _) := SNew emptySub  }.

Equations subComplement {n : nat} (s : Sub n) : Sub n :=
subComplement SEmpty    := SEmpty;
subComplement (SNew t)  := SOld (subComplement t);
subComplement (SOld t)  := SNew (subComplement t).


Inductive InSub : forall {n : nat}, Sub n -> Fin.t n -> Prop :=
   | NewIn    : forall {n : nat} (s : Sub n), InSub (SNew s) (FL n)
   | OldInOld : forall {n : nat} {s : Sub n} {x : Fin.t n} (xInS : InSub s x),
                                           InSub (SOld s) (FU x)
   | OldInNew : forall {n : nat} {s : Sub n} {x : Fin.t n} (xInS : InSub s x),
                                           InSub (SNew s) (FU x).

(*
Equations decInSub {n : nat} (s : Sub n) (x : Fin.t n) : 
                   decidable (InSub s x) :=
decInSub {n:=0}  _  x  :=! x;
decInSub {n:=(S _)} (SNew s) x with finFUOrFL x := {
                               | (inl (existT y eq (* x = FU y *))) 
                                   with decInSub s y := {
                                   | (or_introl yInS)  := _;
                                   | (or_intror yNiS) := _};
                               | (inr eq) (* x = FL _ *) := or_introl _};
decInSub {n:=(S _)} (SOld s) x with finFUOrFL x := {
                               | (inl (existT y eq (* x = FU y *)))
                                   with decInSub s y := {
                                   | (or_introl yInS)  := _;
                                   | (or_intror yNiS) := _};
                               | (inr eq) (* x = FL _ *) :=
                                                  or_intror _}.
Next Obligation.
  left. exact (OldInNew yInS).
Defined.
Next Obligation.
  right. intro.  H.
  ...?
*)


(* a subset s defines an equivalence relation that
   connects the elements of s *)

(* we need a type that has an equivalence and maybe a
   distinguished equivalence class  *)

Definition EqRMaybeStar (n : nat) : Type :=
          { d : nat & (ER n d * option (Fin.t d))%type}.


Equations eqrFromSub' {n : nat} (s : Sub n) : EqRMaybeStar n :=
eqrFromSub' SEmpty := (existT _ 0 (EREmpty , None));
(* this complains about non-exhaustive pattern matching ???
eqrFromSub' (SOld s) with (eqrFromSub' s) := {
                                | (existT _ d (pair e None))
                                  := existT _ (S d) (ERNew e, None);
                                | (existT _ d (pair e (Some t)))
                                  := existT _ (S d) (ERNew e , Some (FU t))};
eqrFromSub' (SNew s) with (eqrFromSub' s) := {
                                | (existT _ d (pair e None))
                                  := existT (S d) (ERNew e , Some (FL d));
                                | (existT _ d (pair e (Some t)))
                                  := existT _ d (ERPut t e , Some t)}.
so we have to do it with holes: *)
eqrFromSub' (SOld s) with (eqrFromSub' s) := {
                                |IH := _};
eqrFromSub' (SNew s) with (eqrFromSub' s) := {
                                |IH := _}.
Next Obligation.
  destruct IH as [d [e [t|]]]; exists (S d).
  - exact (ERNew e , Some (FU t)).
  - exact (ERNew e , None).
Defined.
Next Obligation.
  destruct IH as [d [e [t|]]].
  - exists d. exact (ERPut t e , Some t).
  - exists (S d). exact (ERNew e , Some (FL d)).
Defined.


(* subsets ... 2nd attempt *)

Inductive SS : nat -> nat -> Type :=
  | SSEmpty : SS 0 0
  | SSNew   : forall {c m : nat}, SS c m -> SS (S c) (S m)
  | SSSkip  : forall {c m : nat}, SS c m -> SS    c  (S m).

Equations ssMap  {c m : nat} (s : SS c m) : Vector.t (Fin.t m) c :=
ssMap  SSEmpty    := nil;
ssMap (SSNew s')  := shiftin (FL _) (map FU (ssMap s'));
ssMap (SSSkip s') :=                (map FU (ssMap s')).





(* not needed...
Equations leDichoAlt (n m : nat) (nLEm : n <= m) (mLn : m < n) : False :=
leDichoAlt n ?(n) le_n y := nleSuccDiagL _ y;
leDichoAlt n _ (le_S nLEm) y <= leTrans _ _ _ y nLEm =>
             | SSmLEm  <= leTrans _ _ _ (le_S _ _ (le_n _)) SSmLEm => 
             | SmLEm := nleSuccDiagL _ SmLEm.

Equations leDicho2 (n m : nat) (nLEm : n <= m) : (n = m) + (n < m) :=
leDicho2 n m nLEm <= ltTricho n m =>
          | (inl (inl mEQn)) := inl (eq_sym mEQn);
          | (inl (inr mLTn)) := False_rect _ (leDichoAlt n m nLEm mLTn);
          | (inr nLTm)       := inr nLTm.
*)


