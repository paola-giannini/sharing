Require Import Decidable.
Require Import Arith.
Require Import NatMisc.
Require Import DecidableEquivalences.
Require Import Fin.
Require Import Vector.
Require Import FinVectorMisc.
Import VectorNotations.
Require Import SigmaMisc.
Require Import NotationsMisc.
From Equations Require Import Equations.
Set Equations Transparent.
Unset Equations WithK.

(** Equivalence relations on {0,1,...,n-1} **)

(* To build a type of all equivalence relations on {0,1,...,n-1}, just
   describe the process of putting elements into their classes one by one:

   - start with an empty list of classes
   - assuming {0,1,...,n-1} have been put into classes already, either
     + the element n is not related to any of the lower elements,
       thus forming a new class, or
     + n belongs to one of the existing classes.

   This translates into an inductive type family indexed by the number
   of elements and the number of classes: *)

Inductive ER : nat -> nat -> Type :=
  | EREmpty             :                      ER O O
  | ERNew   {n c : nat} :            ER n c -> ER (S n) (S c)
  | ERPut   {n c : nat} : Fin.t c -> ER n c -> ER (S n) c.

Notation "#"        :=  EREmpty.
Notation "e '<*'"   := (ERNew e)   (at level 70).
Notation "e '<<' x" := (ERPut x e) (at level 69, left associativity).

(* ... unfortunately, [<*] and [<<}  cannot be used in patterns 
   of "Equations" *)

(* the type of all equivalence relations on {0,...,n-1} becomes: *)

Definition EqR (n : nat) : Type := { c : nat & ER n c }.

(* the embedding of [ER n c] in [EqR n] *)

Definition erEqr {n c : nat} (e : ER n c) : EqR n := {| c ; e |}.


(* since we have [EqDec] for [nat] and [Fin.t], [EqDec] for [ER] is derivable *)

Derive EqDec for ER.


(* and thus we also have UIP *)

Equations uipER {n c : nat} {e1 : ER n c} (eq : e1 = e1) : eq = eq_refl :=
  uipER eq_refl := eq_refl.


(* derive wellfounded subterm relation for wf recursion *)

Derive Signature Subterm for ER.



(** special equivalence relations **)

(* the identity relation *)

Equations idER {n : nat} : ER n n :=
  idER {n:=O}     := #;
  idER {n:=(S m)} := idER <*.

Definition idEqr {n : nat} : EqR n := {| n ; idER |}.

(* the all relation *)

Equations allER {n : nat} : ER (S n) 1 :=
  allER {n:=O}     := # <*;
  allER {n:=(S m)} := allER << F1.

Equations allEqr {n : nat} : EqR n := 
  allEqr {n:=0}     := {| 0 ; # |};
  allEqr {n:=(S _)} := {| 1 ; allER  |}.


(** elementary properties of [ER] **)

(* any element of [ER 0 0] is equal to EREmpty *)

Equations er00Empty (e : ER 0 0) : e = # :=
  er00Empty # := eq_refl.

(* if [ER n c] is inhabited, then [c <= n] *)

Equations erCLeN {n c : nat} (e : ER n c) : c <= n :=
  erCLeN  #          := @le_n 0;
  erCLeN (ERNew e)   := leNS (erCLeN e);
  erCLeN (ERPut t e) := le_S _ _ (erCLeN e).

(* [idER n] is the only element of [ER n n] *)

Equations ernnIdER {n : nat} (e : ER n n) : e = idER :=
  ernnIdER  e by rec (signature_pack e) ER_subterm :=
  ernnIdER  #          := eq_refl;
  ernnIdER (ERNew e)   := f_equal ERNew (ernnIdER e);
  ernnIdER (ERPut t e) := False_rect _ (nleSuccDiagL _ (erCLeN e)).

(* any equivalence relation with exactly 1 class is [allER] *)

Equations ern1AllER {n : nat} (e : ER (S n) 1) : e = allER :=
  ern1AllER {n:=0}     (ERNew #)           :=  eq_refl;
  ern1AllER {n:=(S _)} (ERNew (ERPut t _)) :=! t;
  ern1AllER {n:=(S _)} (ERPut F1 e)        :=  f_equal (ERPut F1) (ern1AllER e).


(** elementary properties of [EqR] **)

(* the only element in [EqR] 0 is [idEqr] ( which is [{| 0 ; # |}]) *)

Equations eqr0Id (e : EqR 0) : e = idEqr :=
  eqr0Id {| 0 ; # |} := eq_refl.


(** [erMap] **)

(* [erMap e] is the Vector of length [n], with the [e]-class of the [i]th
   element of [Fin.t n] at the [i]th position. I.e., it is the tabulation
   of the map sending an element to its equivalence class.

   [ER] is built by adding the last element of a [Fin], so we have to use
   [FL], [FU] and [shiftin] (a.k.a. [snoc]) instead of [F1], [FS] and [Cons]. *)

Equations erMap {n c : nat} (e : ER n c) : Vector.t (Fin.t c) n :=
  erMap  #          := [];
  erMap (ERNew e)   := shiftin (FL _) (map FU (erMap e));
  erMap (ERPut t e) := shiftin  t             (erMap e).

Notation "e '@v' t" := (Vector.nth (erMap e) t) 
                       (at level 61, right associativity).

(* computation lemmata for [@v] *)

Lemma erMapNewLast {n c : nat} (e : ER n c) :
                   (e <*) @v FL n = FL c.
Proof. apply shiftinLast. Defined.

Lemma erMapNewPrevious {n c : nat} (e : ER n c) (y : Fin.t n) :
                       (e <*) @v FU y = FU (e @v y).
Proof. rewrite shiftinPrevious; apply nthMapLemma. Defined.

Lemma erMapPutLast {n c : nat} (e : ER n c) (t : Fin.t c) :
                   (e << t) @v (FL n) = t.
Proof. apply shiftinLast. Defined.

Lemma erMapPutPrevious {n c : nat} (e : ER n c)
                       (t : Fin.t c) (y : Fin.t n) :
                       (e << t) @v (FU y) = (e @v y).
Proof. apply shiftinPrevious. Defined.

Ltac erMapRewrites := try repeat
   (rewrite erMapNewLast     ||
    rewrite erMapNewPrevious ||
    rewrite erMapPutLast     ||
    rewrite erMapPutPrevious).


(** properties of [@v] **)

(* erMap of idER is the identity *)

Equations(noind) idERId {n : nat} (x : Fin.t n) : idER @v x = x :=
  idERId {n:=0}     x                  :=! x;
  idERId {n:=(S _)} x with finFUOrFL x := {
                      | (inl {| y ; eq |}) (* x = FU y *) :=
                         idER @v x      ={ f_equal _ eq }=
                         idER @v (FU y) ={ erMapNewPrevious idER y }=
                         FU (idER @v y) ={ f_equal FU (idERId y) }=
                         FU y           ={ eq_sym eq }=
                         x              QED;
                      | (inr eq) (* x = FL _ *) :=
                         idER @v x      ={ f_equal _ eq }=
                         idER @v (FL _) ={ erMapNewLast idER }=
                         FL _           ={ eq_sym eq }=
                         x              QED}.


(** erSection **)

(* [erSection e] maps each class to its smallest representative *)

Equations erSection {n c : nat} (e : ER n c) : Vector.t (Fin.t n) c :=
  erSection  #          := [];
  erSection (ERNew e)   := shiftin (FL _) (map FU (erSection e));
  erSection (ERPut _ e) :=                (map FU (erSection e)).

Notation "e '@^' cl" := (Vector.nth (erSection e) cl)
                        (at level 61, right associativity).

(* computation lemmata for [@^] *)

Lemma erSectionNewLast {n c : nat} (e : ER n c) :
                       (e <*) @^ (FL c) = FL n.
Proof. apply shiftinLast. Defined.

Lemma erSectionNewPrevious {n c : nat} (e : ER n c) (y : Fin.t c) :
                           (e <*) @^ (FU y) = FU (e @^ y).
Proof. rewrite shiftinPrevious; apply nthMapLemma. Defined.

Lemma erSectionPut {n c : nat} (e : ER n c) (t x : Fin.t c) :
                   (e << t) @^ x = FU (e @^ x).
Proof. apply nthMapLemma. Defined.

Ltac erSectionRewrites := try repeat
   (rewrite erSectionNewLast     ||
    rewrite erSectionNewPrevious ||
    rewrite erSectionPut).

Ltac erRewrites := try repeat (erMapRewrites || erSectionRewrites).

(* [erSection e] is a section of [erMap e] *)

Lemma erSectionIsSection {n c : nat} (e : ER n c) (y : Fin.t c) :
                          e @v e @^ y = y.
Proof.
  induction e.
  - apply (Fin.case0 _ y).
  - destruct (finFUOrFL y) as [[y' eq]|eq]; rewrite eq; erRewrites.
    + apply f_equal. apply IHe.
    + reflexivity.
  - erRewrites.
    apply IHe.
Defined.

(* thus it is injective *)

Lemma erSectionIsInjective {n c : nat} (e : ER n c) (y1 y2 : Fin.t c) :
                           e @^ y1 = e @^ y2 <-> y1 = y2.
Proof.
  split; intro eq.
  + pose (f_equal (fun y => e @v y) eq) as eq'; simpl in eq'.
    repeat rewrite erSectionIsSection in eq'.
    exact eq'.
  + apply f_equal. exact eq.
Defined.

(** [erClassMin] **)

(* [erMap e] followed by [erSection e] maps any element to the smallest element
   in its equivalence class *)

Definition erClassMin {n c : nat} (e : ER n c) :
                       Vector.t (Fin.t n) n :=
  Vector.map (fun x => e @^ x) (erMap e).

Notation "e '@<' x" := (Vector.nth (erClassMin e) x) 
                       (at level 61, right associativity).

(* [e @<] is [e @v] followed by [e @^] *)

Lemma erClassMinExpand {n c : nat} (e : ER n c) (x : Fin.t n) :
                       e @< x = e @^ e @v x.
Proof. apply nthMapLemma. Defined.

(* [e @<] is idempotent *)

Lemma erClassMinIsIdempotent {n c : nat} (e : ER n c) (x : Fin.t n) :
                              e @< e @< x = e @< x.
Proof.
  repeat rewrite erClassMinExpand.
  rewrite erSectionIsSection.
  reflexivity.
Defined.

(* computation lemmata for [@<] *)

Ltac erSimplify := try repeat 
   (rewrite erClassMinIsIdempotent ||
    rewrite erClassMinExpand       ||
    rewrite erSectionIsSection     ||
    rewrite erSectionIsInjective   ||
    erRewrites                     ||
    trivial).

Lemma erClassMinNewLast {n c : nat} (e : ER n c) :
                        (e <*) @< (FL n) = FL n.
Proof. erSimplify. Defined.

Lemma erClassMinNewPrevious {n c : nat} (e : ER n c) (y : Fin.t n) :
                            (e <*) @< (FU y) = FU ( e @< y ).
Proof. erSimplify. Defined.

Lemma erClassMinPutLast {n c : nat} (e : ER n c) (t : Fin.t c) :
                        (e << t) @< (FL n) = FU (e @^ t).
Proof. erSimplify. Defined.

Lemma erClassMinPutPrevious {n c : nat} (e : ER n c) (t : Fin.t c) (x : Fin.t n) :
                            (e << t) @< (FU x) = FU (e @< x).
Proof. erSimplify. Defined.

Ltac erSimplify2 := try repeat
  (rewrite erClassMinNewLast      ||
   rewrite erClassMinNewPrevious  ||
   rewrite erClassMinPutLast      ||
   rewrite erClassMinPutPrevious  ||
   (* have to put also these here ...*)
   rewrite shiftinPrevious        ||
   rewrite shiftinLast            ||
   rewrite nthMapLemma            ||
   erSimplify).

Obligation Tactic := program_simpl; erSimplify2.

(** [eqrClassMin] **)

(* the result type of [erClassMin e] is not dependent on c, so we can define *)

Definition eqrClassMin {n : nat} (e : EqR n) :
                        Vector.t (Fin.t n) n :=
  erClassMin (e.2).

Notation "e '@@' x" := (Vector.nth (eqrClassMin e) x)
                       (at level 61, right associativity).

(* trivial computation lemma for [@@] *)

Lemma eqrClassMinCompute {n c : nat} (e : ER n c) (x : Fin.t n) :
                         {| c ; e |} @@ x = e @< x.
Proof. trivial. Defined.

(* [e @@] is idempotent *)

Lemma eqrClassMinIsIdempotent {n : nat} (e : EqR n) (x : Fin.t n) :
                               e @@ e @@ x = e @@ x.
Proof.
  destruct e as [c e].
  erSimplify2.
Defined.

Ltac erSimplify3 := try repeat
    (rewrite eqrClassMinIsIdempotent  ||
     rewrite eqrClassMinCompute       ||
     apply (f_equal FU)   ||
     erSimplify2).

Obligation Tactic := program_simpl; erSimplify3.


(** map to normally defined decidable equivalence relations on [Fin.t n] *)

(* The relation on [Fin.t n] defined by [e : EqR] is just the kernel of
   [eqrClassMin], i.e. the pullback of equality along [eqrClassMin].
   It is a decidable equivalence on [Fin.t n], as equality has this property
   and pullback preserves it.  *)

Definition eqrToDecEq {n : nat} (e : EqR n) :
                       DecidableEquivalence (Fin.t n) :=
  pullbackDecidableEquivalence (fun x => e @@ x) eqFinDecidableEquivalence.

Notation "x '~(' e ')~' y" := (relationOfDecidableEquivalence (eqrToDecEq e) x y)
                              (at level 62).

(* needed to shorten proofs *)

Lemma eqrToDecEqCompute {n : nat} (e : EqR n) (x y : Fin.t n) : 
                        x ~(e)~ y  <-> e @@ x = e @@ y.
Proof.
  unfold eqrToDecEq; simpl; unfold pullbackRelation.
  reflexivity.
Defined.


(** composition **)

Equations erCompose {n c d: nat} (e1 : ER n c) (e2 : ER c d) :
                     ER n d :=
  erCompose  #             #            :=  #;
  erCompose (ERNew e1)    (ERNew e2)    := (erCompose e1 e2) <* ;
  erCompose (ERNew e1)    (ERPut t2 e2) := (erCompose e1 e2) << t2;
  erCompose (ERPut t1 e1)  e2           := (erCompose e1 e2) << (e2 @v t1).

Notation  "e1 '**' e2" := (@erCompose _ _ _ e1 e2)
                          (at level 60, right associativity).


(** properties of [erCompose] **)

(* [idER] is left unit for [**] *)

Equations idERLeft1 {n c : nat} (e : ER n c) :
                     idER ** e = e :=
  idERLeft1   #          := eq_refl;
  idERLeft1  (ERNew e)   := f_equal  ERNew    (idERLeft1 e);
  idERLeft1  (ERPut t e) := f_equal (ERPut t) (idERLeft1 e).

(* [idER] is right unit for [**] *)

Equations idERRight1 {n c : nat} (e : ER n c) :
                      e ** idER = e :=
idERRight1  #          :=  eq_refl;
idERRight1 (ERNew e)   := (f_equal ERNew (idERRight1 e));
idERRight1 (ERPut t e) := 
  (e << t) ** idER
     ={ erCompose_equation_4 _ _ _ _ _ _ }=
  (e ** idER) << (idER @@ t)
     ={ f_equal (fun s => (e ** idER) << s ) (idERId t) }=
  (e ** idER) << t 
     ={ f_equal (ERPut t) (idERRight1 e ) }=
  (e << t) QED.

(* postcomposing with [allER] maps to [allER] *)

Definition allERRight {n d : nat} (e : ER (S n) (S d)) :
                       e ** allER = allER.
Proof. apply ern1AllER. Defined.


(* [erMap] of [e1 ** e2] is composition of erMaps *)

Equations(noind) erMapCompose {n m l : nat} (e1 : ER n m) (e2 : ER m l) 
                              (x : Fin.t n) :
                              (e1 ** e2) @v x = e2 @v (e1 @v x) :=
  erMapCompose  e1 e2 x by rec (signature_pack e1) ER_subterm :=
  erMapCompose  #            #             x                  :=! x;
  erMapCompose (ERNew e1)   (ERNew e2)     x with finFUOrFL x := {
               | (inl {| y ; eq |}) with erMapCompose e1 e2 y := { | IH := _};
               | (inr eq) := _};
  erMapCompose (ERNew e1)   (ERPut t2 e2)  x with finFUOrFL x := {
               | (inl {| y ; eq |}) with erMapCompose e1 e2 y := { | IH := _};
               | (inr eq) := _};
  erMapCompose (ERPut t1 e1) e2            x with finFUOrFL x := {
               | (inl {| y ; eq |}) with erMapCompose e1 e2 y := { | IH := _};
               | (inr eq) := _}.


(* [erSection] of [e1 ** e2] is composition of [erSection]s.
   Note the order! *)

Equations(noind) erSectionCompose {n m l : nat} (e1 : ER n m) (e2 : ER m l) 
                                  (x : Fin.t l) :
                                  (e1 ** e2) @^ x = e1 @^ (e2 @^ x) :=
  erSectionCompose  e1 e2 x by rec (signature_pack e1) ER_subterm :=
  erSectionCompose  #           #         x                  :=! x;
  erSectionCompose (ERNew e1)  (ERNew e2) x with finFUOrFL x := {
                   | (inl {| y ; eq |}) 
                      with erSectionCompose e1 e2 y := { | IH := _ };
                   | (inr eq) := _};
  erSectionCompose (ERNew e1)  (ERPut _ e2) x
                      with erSectionCompose e1 e2 x := { | IH := _ };
  erSectionCompose (ERPut _ e1) e2        x
                      with erSectionCompose e1 e2 x := { | IH := _ }.


Ltac erSimplify4 := try repeat
  (rewrite erMapCompose     ||
   rewrite erSectionCompose ||
   erSimplify3).

Ltac erSimplifyIn H :=
   generalize H; erSimplify4; clear H; intro H.

Obligation Tactic := program_simpl; erSimplify4.

(* [**] is associative *)

Lemma erComposeAssociative {n m l k : nat}
                           (e1 : ER n m) (e2 : ER m l) (e3 : ER l k) :
                           (e1 ** e2) ** e3 = e1 ** e2 ** e3.
Proof.
  funelim (e1 ** e2).
  - funelim (# ** e3). reflexivity.
  - funelim (((e ** e0) <*) ** e3); erSimplify4; rewrite H1; trivial.
  - repeat (rewrite erCompose_equation_4).
    rewrite erCompose_equation_3. rewrite H. trivial.
  - repeat (rewrite erCompose_equation_4).
    rewrite H. rewrite erMapCompose. trivial.
Defined.


(** containment **)

(* [f] is contained in [e]
   <=> any equivalence class of [f] is contained in an equivalence class of [e],
   <=> the classes of [e] are unions of certain classes of [f],
   <=> there is an equivalence [d] on the set of classes of [f] s.t. the union 
       of all classes of [f] in a class of [d] is a class of e ( 8-( ),
   <=> there exists [d] such that  [f ** d = e]  *)

Definition erContains {n m l : nat} (f: ER n m) (e: ER n l) :
                       Type := { d : ER m l & f ** d = e }.

Notation "f '[='  e" := (erContains f e) (at level 50).

Definition eqrContains {n : nat} (f e : EqR n) : Type := f.2 [= e.2.

Notation "e 'C='  f" := (eqrContains e f) (at level 50).

(** properties of [[=] and [C=] **)

(* [[=] is Reflexive and Transitive *)

Definition erContainsReflexive {n m : nat} (e : ER n m) : 
                               e [= e :=
  {| idER ; (idERRight1 e) |}.

Definition erContainsTransitive {n c1 c2 c3 : nat} (e1 : ER n c1) 
                                (e2 : ER n c2) (e3 : ER n c3) :
                                (e1 [= e2) -> (e2 [= e3) -> (e1 [= e3).
Proof.
  intros [d1 eq1] [d2 eq2].
  exists (d1 ** d2).
  rewrite <- erComposeAssociative.
  rewrite eq1.
  exact eq2.
Defined.

(* [C=]  is a partial order i.e. reflexive, transitive and antisymmetric *)

Definition eqrContainsReflexive {n : nat} (e : EqR n) : 
                                 e C= e := erContainsReflexive e.2.

Definition eqrContainsTransitive {n : nat} (e1 e2 e3 : EqR n) :
                                 (e1 C= e2) -> (e2 C= e3) -> (e1 C= e3).
Proof. apply erContainsTransitive. Defined.

Lemma eqrContainsAntiSymmetric {n : nat} (e1 e2 : EqR n) :
                               (e1 C= e2) -> (e2 C= e1) -> e1 = e2.
Proof.
  destruct e1 as [c1 e1]; destruct e2 as [c2 e2].
  intros [d1 eq1] [d2 eq2]; simpl in *.
  destruct (leAntiSymmetric _ _ (conj (erCLeN d2) (erCLeN d1))).
  rewrite (ernnIdER d1) in eq1.
  rewrite (idERRight1 e1) in eq1.
  rewrite eq1.
  reflexivity.
Defined.

(* [idEqr] is minimal for [C=] *)

Equations idEqrMin {n : nat} (e : EqR n) :
                     idEqr C= e :=
idEqrMin {|_; e |} := {| e; idERLeft1 e |}.

(* [allEqr] is maximal for [C=] *)

Equations allEqrMax {n : nat} (e : EqR n) :
                     e C= allEqr :=
  allEqrMax {n:=0}     {| 0 ; # |}      := eqrContainsReflexive _;
  allEqrMax {n:=(S _)} {| 0 ; _ << t |} :=! t;
  allEqrMax {n:=(S _)} {|(S _); e |}    := {| allER ; allERRight e |}.


(** [eqrToDecEq] preserves and reflects containment **)

(* rewrite to expand definition of [c=] ... just to shorten proofs *)

Lemma eqrToDecEqContainsRewrite {n : nat} (e f : EqR n) :
                                (eqrToDecEq e) c= (eqrToDecEq f) <-> 
                                (forall x y : Fin.t n, 
                                 e @@ x = e @@ y -> f @@ x = f @@ y).
Proof.
  unfold "c=", Relations_1.contains, eqrToDecEq, pullbackDecidableEquivalence,
         pullbackRelation; simpl.
  reflexivity.
Defined.

(* containment is preserved by [eqrToDecEq] *)

Lemma eqrToDecEqPreservesContains {n : nat} (e f : EqR n) (p : e C= f) :
                                  (eqrToDecEq e) c= (eqrToDecEq f).
Proof.
  destruct e as [c e], f as [d f], p as [g eq]; simpl in *.
  rewrite eqrToDecEqContainsRewrite.
  intros x y.
  repeat rewrite <- eq.
  erSimplify4.
  apply f_equal.
Defined.

(* to show that [eqrToDec] also reflects containment, we first show that
   [(eqrToDecEq e) c= (eqrToDecEq f)]  is equivalent to have 
   [(e @@ x) ~(f)~ x]  for any [x]  *)

Definition eqrMinMapCondition {n : nat} (e f : EqR n) : Prop :=
  forall (x : Fin.t n), (e @@ x) ~(f)~ x.

Lemma eqrMinMapConditionIffEqrToDecEqContains
                          {n : nat} (e f : EqR n) :
                          eqrMinMapCondition e f <->
                          (eqrToDecEq e) c= (eqrToDecEq f).
Proof.
  destruct e as [k e], f as [l f].
  split.
  + intro emmc.
    rewrite eqrToDecEqContainsRewrite.
    intros x y eRel;  simpl.
    rewrite <- (emmc x).
    rewrite <- (emmc y).
    rewrite eRel. reflexivity.
  + intro ec.
    rewrite eqrToDecEqContainsRewrite in ec.
    intro x.
    rewrite eqrToDecEqCompute.
    apply ec.
    apply eqrClassMinIsIdempotent.
Defined.

(* If [e C= f], [eqrMinMapCondition e f] holds *)

Ltac handleFinCase0 n := try (destruct n; [> apply Fin.case0; trivial | idtac]).

Lemma eqrContainsToEqrMinMapCondition 
                          {n : nat} (e f : EqR n) (cont: e C= f) :
                          eqrMinMapCondition e f.
Proof.
  intro x.
  handleFinCase0 n.
  rewrite eqrToDecEqCompute.
  destruct e as [c1 e], f as [c3 f], cont as [c eq]; simpl in *.
  rewrite <- eq.
  erSimplify4.
Defined.

(* that [eqrMinMapCondition e f] implies [e C= f] is a little more difficult *)

(* Restrict equivalence on [n+1] elements to the first [n] elements
   Just take the constructor argument of the 2nd component and repack it.
   Needed only to shorten statements. *)

Equations eqrShrink {n : nat} (e : EqR (S n)) :
                    EqR n :=
  eqrShrink {|_ ; e <*  |} := {|_ ; e |};
  eqrShrink {|_ ; e << _|} := {|_ ; e |}.

(* on the lower elements, [eqrShrink e] does "essentailly the same" as [e] *)

Lemma eqrShrinkClassMin {n : nat} (e : EqR (S n)) (x : Fin.t n) :
                        FU ((eqrShrink e) @@ x) = e @@ (FU x).
Proof.
  destruct e as [k e].
  dependent induction e.
  - rewrite eqrShrink_equation_1. apply eq_sym. erSimplify4.
  - rewrite eqrShrink_equation_2. apply eq_sym. erSimplify4.
Defined.

Lemma eqrShrinkPreservesEqrMinMapCondition 
                        {n : nat} (e f : EqR (S n)) 
                        (emms : eqrMinMapCondition e f) :
                        eqrMinMapCondition (eqrShrink e) (eqrShrink f).
Proof.
  unfold eqrMinMapCondition, eqrToDecEq in *; simpl in *;
  unfold pullbackRelation in *. (* lowlevel rewrites really necessary ?? *)
  intro x.
  apply fuIsInjective.
  repeat rewrite eqrShrinkClassMin.
  apply emms.
Defined.

(* [eqrShrink] preserves containment *)

Equations eqrShrinkPreservesContains {n : nat} (e f : EqR (S n)) (p : e C= f) :
                                     (eqrShrink e) C= (eqrShrink f) :=
  eqrShrinkPreservesContains {|_;_<*|}  {|_;_<* |} {|d<* ;eq|} := {|d;sigmaNat2 _|};
  eqrShrinkPreservesContains {|_;_<*|}  {|_;_<* |} {|_<<_;eq|} :=! eq;
  eqrShrinkPreservesContains {|_;_<*|}  {|_;_<<t|} {|_<* ;eq|} :=! eq;
  eqrShrinkPreservesContains {|_;_<*|}  {|_;_<<t|} {|d<<_;eq|} := {|d;sigmaNat2 _|};
  eqrShrinkPreservesContains {|_;_<<_|} {|_;_<* |} {|_   ;eq|} :=! eq;
  eqrShrinkPreservesContains {|_;_<<_|} {|_;_<<_|} {|d   ;eq|} := {|d;sigmaNat2 _|}.


(* to prove [e C= f], it is enough to have containment of the shrinks and
   [eqrMinMapCondition e f (FL n)]  *)

Equations eqrBuildContains {n : nat} (e f :  EqR (S n))
                           (shrinkCond : (eqrShrink e) C= (eqrShrink f))
                           (flCond     : f @@ e @@ (FL n) = f @@ (FL n )) :
                            e C= f :=
  eqrBuildContains {|_; e<*   |} {|_; f<*   |} {|c; eq |} _   := {|c<*   ;_|};
  eqrBuildContains {|_; e<*   |} {|_; f<<t2 |} {|c; eq |} _   := {|c<<t2 ;_|};
  eqrBuildContains {|_; e<<t1 |} {|_; f<*   |} shrinkC    flC := _;
  eqrBuildContains {|_; e<<t1 |} {|_; f<<t2 |} {|c; _  |} flC := {|c ;_|}.
Next Obligation.
  clear shrinkC.
  handleFinCase0 wildcard1.
  apply False_rect.
  erSimplifyIn flC.
  apply (finNotFUAndFL _ flC).
Defined.
Next Obligation.
  handleFinCase0 wildcard1.
  cut (c @v t1 = t2).
  - intro eq. rewrite eq. reflexivity.
  - erSimplifyIn flC.
    apply fuIsInjective in flC.
    repeat apply erSectionIsInjective in flC.
    exact flC.
Defined.

(* thus, [erqMinMapCondition e f] implies [e C= f] *)

Lemma eqrContainsFromEqrMinMapCondition 
                          {n : nat} (e f : EqR n)
                          (emmc : eqrMinMapCondition e f) :
                           e C= f.
Proof.
  induction n.
  - rewrite (eqr0Id e). apply idEqrMin.
  - apply eqrBuildContains.
    + apply IHn.
      apply eqrShrinkPreservesEqrMinMapCondition.
      exact emmc.
    + apply emmc.
Defined.

(* and we have that [eqrToDecEq] reflects containment *)

Lemma eqrToDecEqReflectsContains {n : nat} (e f : EqR n)
                                 (etdeContains : (eqrToDecEq e) c= (eqrToDecEq f)) :
                                 e C= f.
Proof.
  apply eqrContainsFromEqrMinMapCondition.
  rewrite eqrMinMapConditionIffEqrToDecEqContains .
  exact etdeContains.
Defined.


(* meet *)

Lemma eqrContainedInNewFL {n c1 : nat} (e : EqR (S n)) (e1 : ER n c1) 
           (cont : e C= {|_; e1 <*|}) :
            e @@ FL _ = FL _.
Proof.
  destruct e as [c e].
  dependent destruction e.
  - apply erClassMinNewLast.
  - handleFinCase0 c.
    apply False_rect.
    pose (eqrContainsToEqrMinMapCondition _ _ cont (FL _)) as mmcFL.
    rewrite eqrToDecEqCompute in mmcFL.
    erSimplifyIn mmcFL.
    apply (finNotFUAndFL _ mmcFL).
Defined.

Equations eqrMeet (n : nat) (e1 e2 : EqR n) :
                  { e : EqR n & ( (e C= e1) * (e C= e2) * 
                                   forall e' : EqR n,
                                          e' C= e1 -> e' C= e2 -> 
                                          e' C= e )%type } :=
eqrMeet n e1 e2 by rec n lt :=
eqrMeet 0     {|_; #    |}  {|_; #    |} := {| {|0;#|} ; _ |};
eqrMeet (S _) {|_; e1<* |}  {|_; e2<* |}  with (eqrMeet _ {|_;e1|} {|_;e2|}) := {
                                         | {| {| d3 ; e3 |} ; (c1,c2,uni) |} :=
                                           {| {|_; e3 <* |}; _ |}  };
eqrMeet (S _) {|_; e1<<t1|} {|_; e2<* |}  with (eqrMeet _ {|_;e1|} {|_;e2|}) := {
                                         | {| {| d3 ; e3 |} ; (c1,c2,uni) |} :=
                                           {| {|_; e3 <* |}; _ |}  };
eqrMeet (S _) {|_; e1<* |}  {|_; e2<<t2|} with (eqrMeet _ {|_;e1|} {|_;e2|}) := {
                                         | {| {| d3 ; e3 |} ; (c1,c2,uni) |} :=
                                           {| {|_; e3 <* |}; _ |}  };
eqrMeet (S _) {|_; e1<<t1|} {|_; e2<<t2|} with (eqrMeet _ {|_;e1|} {|_;e2|}) := {
                                         | {| {| d3 ; e3 |} ; (c1,c2,uni) |} :=
                                           {| {|_; e3 << _ |}; _ |}  }.
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
  - split; apply eqrBuildContains.
    + exact c1.
    + erSimplify4.
    + exact c2.
    + erSimplify4.
  - intros e4 e4In1 e4In2.
    apply eqrBuildContains.
    + exact (uni (eqrShrink e4) (eqrShrinkPreservesContains _ _ e4In1)
                                (eqrShrinkPreservesContains _ _ e4In2)).
    + assert (e4 @@ FL _ = FL _) as eq by (apply (eqrContainedInNewFL _ _ e4In1)).
      rewrite eq; reflexivity.
Defined.
Next Obligation.
  clear eqrMeet.
  split.
  - split; apply eqrBuildContains.
    + exact c1.
    + erSimplify4.
    + exact c2.
    + erSimplify4.
  - intros e4 e4In1 e4In2; apply eqrBuildContains.
    + exact (uni (eqrShrink e4) (eqrShrinkPreservesContains _ _ e4In1)
                                (eqrShrinkPreservesContains _ _ e4In2)).
    + assert (e4 @@ FL _ = FL _) as eq by (apply (eqrContainedInNewFL _ _ e4In1)).
      rewrite eq; reflexivity.
Defined.
Next Obligation.
  clear eqrMeet.
  split.
  - split; apply eqrBuildContains.
    + exact c1.
    + erSimplify4.
    + exact c2.
    + erSimplify4.
  - intros e4 e4In1 e4In2; apply eqrBuildContains.
    + exact (uni (eqrShrink e4) (eqrShrinkPreservesContains _ _ e4In1)
                                (eqrShrinkPreservesContains _ _ e4In2)).
    + assert (e4 @@ FL _ = FL _) as eq by (apply (eqrContainedInNewFL _ _ e4In2)).
      rewrite eq; reflexivity.
Defined.
Next Obligation.


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


