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
Notation "'+>' e"   := (ERNew e)   (at level 70).
Notation "x '>>' e" := (ERPut x e) (at level 69, left associativity).

(* Notes
   - unfortunately, [+>] and [>>]  cannot be used in patterns
     of "Equations", this seems to be a limitation of the library itself
   - Formerly, to be consistent with the explanation above, we interpreted
     the largest or last element in Fin.t (S n) as the "new" element to be
     placed into a class. As a consequence, instead of matching against F1 and
     FS, we had to match against "last" and "previous", which became incon-
     venient. So now, in [ERNew e] and [ERPut t e], we interpret e as an 
     equivalence on {FS F1, ...} and F1 as the "new" element (to be put into
     a new class or in class t, resp.).
*)

(* the type of all equivalence relations on {0,...,n-1} becomes: *)

Definition EqR (n : nat) : Type := { c : nat & ER n c }.

(* the embedding of [ER n c] into [EqR n] *)

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
  idER {n:=(S m)} := +> idER.

Definition idEqr {n : nat} : EqR n := {| n ; idER |}.

(* the all relation *)

Equations allER {n : nat} : ER (S n) 1 :=
  allER {n:=O}     := +> # ;
  allER {n:=(S m)} := F1 >> allER.

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
  ernnIdER {n:=0}      #          := eq_refl;
  ernnIdER {n:=(S _)} (ERNew e)   := f_equal ERNew (ernnIdER e);
  ernnIdER {n:=(S _)} (ERPut t e) := False_rect _ (nleSuccDiagL _ (erCLeN e)).

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
   of the map sending an element to its equivalence class. *)

Equations erMap {n c : nat} (e : ER n c) : Vector.t (Fin.t c) n :=
  erMap  #          := [];
  erMap (ERNew e)   := F1 :: (map FS (erMap e));
  erMap (ERPut t e) := t  ::         (erMap e).

Notation "e '@v' t" := (Vector.nth (erMap e) t) 
                       (at level 61, right associativity).

Hint Rewrite @nthMapLemma : eqr.

Obligation Tactic := repeat (simp eqr || program_simpl).


(* computation lemmata for [@v] *)

Equations erMapNewF1 {n c : nat} (e : ER n c) :
                     (+> e) @v F1 = F1 :=
  erMapNewF1 _ := _.

Hint Rewrite @erMapNewF1 : eqr.

Equations erMapNewFS {n c : nat} (e : ER n c) (y : Fin.t n) :
                     (ERNew e) @v (FS y) = FS (e @v y) :=
  erMapNewFS _ _ := _.

Hint Rewrite @erMapNewFS : eqr.

Equations erMapPutF1 {n c : nat} (e : ER n c) (t : Fin.t c) :
                     (t >> e) @v F1 = t :=
  erMapPutF1 _ _ := _.

Hint Rewrite @erMapPutF1 : eqr.

Equations erMapPutFS {n c : nat} (e : ER n c)
                     (t : Fin.t c) (y : Fin.t n) :
                     (t >> e) @v (FS y) = (e @v y) :=
  erMapPutFS _ _ _ := _.

Hint Rewrite @erMapPutFS : eqr.

(** properties of [@v] **)

(* erMap of idER is the identity *)

Equations(noind) idERId {n : nat} (x : Fin.t n) : idER @v x = x :=
  idERId  F1     := _;
  idERId (FS x)  with (idERId x) := { | IH := _}.
Next Obligation.
  apply f_equal.
  assumption.
Defined.

Hint Rewrite @idERId : eqr.

(** erSection **)

(* [erSection e] maps each class to its largest representative
   (w.r.t. the order F1 < (FS F1) < ... *)

Equations erSection {n c : nat} (e : ER n c) : Vector.t (Fin.t n) c :=
  erSection  #          := [];
  erSection (ERNew e)   := F1 :: (map FS (erSection e));
  erSection (ERPut _ e) :=       (map FS (erSection e)).

Notation "e '@^' cl" := (Vector.nth (erSection e) cl)
                        (at level 61, right associativity).

(* computation lemmata for [@^] *)

Equations erSectionNewF1 {n c : nat} (e : ER n c) :
                         (+>e) @^ F1 = F1 :=
  erSectionNewF1 _ := _.

Hint Rewrite @erSectionNewF1 : eqr.

Equations erSectionNewFS {n c : nat} (e : ER n c) (y : Fin.t c) :
                         (+>e) @^ (FS y) = FS (e @^ y) :=
  erSectionNewFS _ _ := _.

Hint Rewrite @erSectionNewFS : eqr.

Equations erSectionPut {n c : nat} (e : ER n c) (t x : Fin.t c) :
                       (t >> e) @^ x = FS (e @^ x) :=
  erSectionPut _ _ _ := _.

Hint Rewrite @erSectionPut   : eqr.


(* [erSection e] is a section of [erMap e] *)

Lemma erSectionIsSection {n c : nat} (e : ER n c) (y : Fin.t c) :
                          e @v e @^ y = y.
Proof.
  induction e; dependent destruction y;
  simp eqr; apply f_equal; apply IHe.
Defined.

Hint Rewrite @erSectionIsSection : eqr.

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

(* maybe not so good?, we'll see *)
Hint Rewrite @erSectionIsInjective : eqr.


(** [erClassMax] **)

(* [erMap e] followed by [erSection e] maps any element to the largest element
   in its equivalence class *)

Definition erClassMax {n c : nat} (e : ER n c) :
                       Vector.t (Fin.t n) n :=
  Vector.map (fun x => e @^ x) (erMap e).

Notation "e '@>' x" := (Vector.nth (erClassMax e) x) 
                       (at level 61, right associativity).

(* [e @>] is [e @v] followed by [e @^] *)

Equations erClassMaxExpand {n c : nat} (e : ER n c) (x : Fin.t n) :
                           e @> x = e @^ e @v x :=
  erClassMaxExpand _ _ := _.

Hint Rewrite @erClassMaxExpand : eqr.

(* [e @>] is idempotent *)

Lemma erClassMaxIsIdempotent {n c : nat} (e : ER n c) (x : Fin.t n) :
                              e @> e @> x = e @> x.
Proof.
  simp eqr.
(*
  repeat rewrite erClassMaxExpand.
  rewrite erSectionIsSection.
  reflexivity.
*)
Defined.

Hint Rewrite @erClassMaxIsIdempotent : eqr.

(* computation lemmata for [@>] *)

Equations erClassMaxNewF1 {n c : nat} (e : ER n c) :
                          (+>e) @> F1 = F1 :=
  erClassMaxNewF1 _ := _.

Hint Rewrite @erClassMaxNewF1 : eqr.

Equations erClassMaxNewFS {n c : nat} (e : ER n c) (y : Fin.t n) :
                          (+>e) @> (FS y) = FS ( e @> y ) :=
  erClassMaxNewFS _ _ := _.

Hint Rewrite @erClassMaxNewFS : eqr.

Equations erClassMaxPutF1 {n c : nat} (e : ER n c) (t : Fin.t c) :
                          (t >> e) @> F1 = FS (e @^ t) :=
  erClassMaxPutF1 _ _ := _.

Hint Rewrite @erClassMaxPutF1 : eqr.

Equations erClassMaxPutFS {n c : nat} (e : ER n c) (t : Fin.t c) (x : Fin.t n) :
                          (t >> e) @> (FS x) = FS (e @> x) :=
  erClassMaxPutFS _ _ _ := _.

Hint Rewrite @erClassMaxPutFS : eqr.


(** [eqrClassMax] **)

(* the result type of [erClassMax e] is not dependent on c, so we can define *)

Definition eqrClassMax {n : nat} (e : EqR n) :
                        Vector.t (Fin.t n) n :=
  erClassMax (e.2).

Notation "e '@@' x" := (Vector.nth (eqrClassMax e) x)
                       (at level 61, right associativity).

(* trivial computation lemma for [@@] *)

Equations eqrClassMaxCompute {n c : nat} (e : ER n c) (x : Fin.t n) :
                             {| c ; e |} @@ x = e @> x :=
  eqrClassMaxCompute _ _ := _.

Hint Rewrite @eqrClassMaxCompute : eqr.

(* [e @@] is idempotent *)

Equations eqrClassMaxIsIdempotent {n : nat} (e : EqR n) (x : Fin.t n) :
                                  e @@ e @@ x = e @@ x :=
  eqrClassMaxIsIdempotent _ _ := _.

Hint Rewrite @eqrClassMaxIsIdempotent : eqr.


(** the decidable equivalence relation on [Fin.t n] defined by [e : EqR n] *)

(* The relation on [Fin.t n] defined by [e : EqR] is just the kernel of
   [eqrClassMax], i.e. the pullback of equality along [eqrClassMax].
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

Hint Rewrite @eqrToDecEqCompute : eqr.

(** composition **)

Equations erCompose {n c d: nat} (e1 : ER n c) (e2 : ER c d) :
                     ER n d :=
  erCompose  #             #            :=  #;
  erCompose (ERNew e1)    (ERNew e2)    :=            +> (erCompose e1 e2);
  erCompose (ERNew e1)    (ERPut t2 e2) :=         t2 >> (erCompose e1 e2);
  erCompose (ERPut t1 e1)  e2           := (e2 @v t1) >> (erCompose e1 e2).

Notation  "e1 '**' e2" := (@erCompose _ _ _ e1 e2)
                          (at level 60, right associativity).


(** properties of [erCompose] **)

(* [idER] is left unit for [**] *)

Equations idERLeft1 {n c : nat} (e : ER n c) :
                     idER ** e = e :=
  idERLeft1   #          := eq_refl;
  idERLeft1  (ERNew e)   := f_equal  ERNew    (idERLeft1 e);
  idERLeft1  (ERPut t e) := f_equal (ERPut t) (idERLeft1 e).

Hint Rewrite @idERLeft1 : eqr.

(* [idER] is right unit for [**] *)

Equations idERRight1 {n c : nat} (e : ER n c) :
                      e ** idER = e :=
idERRight1  #          :=  eq_refl;
idERRight1 (ERNew e)   := (f_equal ERNew (idERRight1 e));
idERRight1 (ERPut t e) :=
  (t >> e) ** idER
     ={ erCompose_equation_4 _ _ _ _ _ _ }=
  (idER @@ t) >> (e ** idER)
     ={ f_equal (fun s => s >> (e ** idER)) (idERId t) }=
  t >> (e ** idER)
     ={ f_equal (ERPut t) (idERRight1 e ) }=
  (t >> e) QED.

Hint Rewrite @idERRight1 : eqr.


(* postcomposing with [allER] maps to [allER] *)

Definition allERRight {n d : nat} (e : ER (S n) (S d)) :
                       e ** allER = allER.
Proof. apply ern1AllER. Defined.

Hint Rewrite @allERRight : eqr.

(* useful in cases with [n : nat] and [x : Fin.t n] among the hypotheses *)

Ltac handleFinCase0 n := try (destruct n; [> apply Fin.case0; trivial | idtac]).

Equations(noind) erMapCompose {n m l : nat} (e1 : ER n m) (e2 : ER m l) 
                              (x : Fin.t n) :
                              (e1 ** e2) @v x = e2 @v (e1 @v x) :=
  erMapCompose {n:=0}      #            #             x          :=! x;
  erMapCompose {n:=(S _)} (ERNew e1)   (ERNew e2)     F1         := eq_refl;
  erMapCompose {n:=(S _)} (ERNew e1)   (ERNew e2)    (FS y)
                             with erMapCompose e1 e2 y := { | IH := _};
  erMapCompose {n:=(S _)} (ERNew e1)   (ERPut t2 e2)  F1         := _;
  erMapCompose {n:=(S _)} (ERNew e1)   (ERPut t2 e2) (FS y)
                             with erMapCompose e1 e2 y := { | IH := _};
  erMapCompose {n:=(S _)} (ERPut t1 e1) e2            F1         := _;
  erMapCompose {n:=(S _)} (ERPut t1 e1) e2           (FS y)
                             with erMapCompose e1 e2 y := { | IH := _}.
(* above typechecks, but takes a long time... *)

Hint Rewrite @erMapCompose : eqr.

(* [erSection] of [e1 ** e2] is composition of [erSection]s.
   Note the order! *)

Equations(noind) erSectionCompose {n m l : nat} (e1 : ER n m) (e2 : ER m l) 
                                  (x : Fin.t l) :
                                  (e1 ** e2) @^ x = e1 @^ (e2 @^ x) :=
  erSectionCompose {n:=0}      #           #            x     :=! x;
  erSectionCompose {n:=(S _)} (ERNew e1)  (ERNew e2)    F1    := eq_refl;
  erSectionCompose {n:=(S _)} (ERNew e1)  (ERNew e2)   (FS y)
                                with erSectionCompose e1 e2 y := { | IH := _ };
  erSectionCompose {n:=(S _)} (ERNew e1)  (ERPut _ e2)  x
                                with erSectionCompose e1 e2 x := { | IH := _ };
  erSectionCompose {n:=(S _)} (ERPut _ e1) e2           x
                                with erSectionCompose e1 e2 x := { | IH := _ }.

Hint Rewrite @erSectionCompose : eqr.

(* [**] is associative *)

Lemma erComposeAssociative {n m l k : nat}
                           (e1 : ER n m) (e2 : ER m l) (e3 : ER l k) :
                           (e1 ** e2) ** e3 = e1 ** e2 ** e3.
Proof.
  funelim (e1 ** e2).
  - funelim (# ** e3). reflexivity.
  - funelim ((+> (e ** e0)) ** e3); simp eqr; rewrite H1; trivial.
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
       of all classes of [f] in a class of [d] is a class of e ( ;-) ),
   <=> there exists [d] such that  [f ** d = e]  *)

Definition erContains {n m l : nat} (f: ER n m) (e: ER n l) : Type :=
                      { d : ER m l & f ** d = e }.

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
  program_simpl.
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
  program_simpl.
Defined.

(* [idEqr] is minimal for [C=] *)

Equations idEqrMin {n : nat} (e : EqR n) :
                     idEqr C= e :=
idEqrMin {|_; e |} := {| e; idERLeft1 e |}.

(* [allEqr] is maximal for [C=] *)

Equations allEqrMax {n : nat} (e : EqR n) :
                     e C= allEqr :=
  allEqrMax {n:=0}     {| 0 ; # |}      := eqrContainsReflexive _;
  allEqrMax {n:=(S _)} {| 0 ; t >> _ |} :=! t;
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
  destruct e as [c e], f as [d f], p as [g eq]; simpl in *; simp eqr.
  rewrite eqrToDecEqContainsRewrite.
  intros x y. simp eqr. intro eq'.
  repeat rewrite <- eq.
  simp eqr. 
  program_simpl.
Defined.

(* to show that [eqrToDec] also reflects containment, we first show that
   [(eqrToDecEq e) c= (eqrToDecEq f)]  is equivalent to have 
   [(e @@ x) ~(f)~ x]  for any [x]  *)

Definition eqrMaxMapCondition {n : nat} (e f : EqR n) : Prop :=
  forall (x : Fin.t n), (e @@ x) ~(f)~ x.

Lemma eqrMaxMapConditionIffEqrToDecEqContains
                          {n : nat} (e f : EqR n) :
                          eqrMaxMapCondition e f <->
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
    apply eqrClassMaxIsIdempotent.
Defined.

(* If [e C= f], [eqrMaxMapCondition e f] holds *)

Lemma eqrContainsToEqrMaxMapCondition 
                          {n : nat} (e f : EqR n) (cont: e C= f) :
                          eqrMaxMapCondition e f.
Proof.
  intro x.
  handleFinCase0 n.
  rewrite eqrToDecEqCompute.
  destruct e as [c1 e], f as [c3 f], cont as [c eq]; simpl in *.
  rewrite <- eq.
  simp eqr.
Defined.

(* that [eqrMaxMapCondition e f] implies [e C= f] is a little more difficult *)

(* Restrict equivalence on [n+1] elements to the first [n] elements
   Just take the constructor argument of the 2nd component and repack it.
   Needed only to shorten statements. *)

Equations eqrShrink {n : nat} (e : EqR (S n)) :
                    EqR n :=
  eqrShrink {|_ ;   +> e |} := {|_ ; e |};
  eqrShrink {|_ ; _ >> e |} := {|_ ; e |}.

(* on the higher elements, [eqrShrink e] does "essentially the same" as [e] *)

Lemma eqrShrinkClassMax {n : nat} (e : EqR (S n)) (x : Fin.t n) :
                        FS ((eqrShrink e) @@ x) = e @@ (FS x).
Proof.
  destruct e as [k e].
  dependent induction e.
  - rewrite eqrShrink_equation_1. apply eq_sym. simp eqr.
  - rewrite eqrShrink_equation_2. apply eq_sym. simp eqr.
Defined.

Hint Rewrite @eqrShrinkClassMax : eqr.

Lemma eqrShrinkPreservesEqrMaxMapCondition 
                        {n : nat} (e f : EqR (S n)) 
                        (emms : eqrMaxMapCondition e f) :
                        eqrMaxMapCondition (eqrShrink e) (eqrShrink f).
Proof.
  unfold eqrMaxMapCondition, eqrToDecEq in *; simpl in *;
  unfold pullbackRelation in *.
  intro x.
  apply FS_inj.
  repeat rewrite eqrShrinkClassMax.
  apply emms.
Defined.

(* [eqrShrink] preserves containment *)

Equations eqrShrinkPreservesContains {n : nat} (e f : EqR (S n)) (p : e C= f) :
                                     (eqrShrink e) C= (eqrShrink f) :=
  eqrShrinkPreservesContains {|_;+>_|}  {|_;+>_ |} {|+>d ;eq|} := {|d;sigmaNat2 _|};
  eqrShrinkPreservesContains {|_;+>_|}  {|_;+>_ |} {|_>>_;eq|} :=! eq;
  eqrShrinkPreservesContains {|_;+>_|}  {|_;t>>_|} {|+>_ ;eq|} :=! eq;
  eqrShrinkPreservesContains {|_;+>_|}  {|_;t>>_|} {|_>>d;eq|} := {|d;sigmaNat2 _|};
  eqrShrinkPreservesContains {|_;_>>_|} {|_;+>_ |} {|_   ;eq|} :=! eq;
  eqrShrinkPreservesContains {|_;_>>_|} {|_;_>>_|} {|d   ;eq|} := {|d;sigmaNat2 _|}.

(* to prove [e C= f], it is enough to have containment of the shrinks and
   [eqrMaxMapCondition e f F1]  *)

Obligation Tactic := idtac.

Equations(noind) eqrBuildContains {n : nat} (e f :  EqR (S n))
                           (shrinkCond : (eqrShrink e) C= (eqrShrink f))
                           (f1Cond     : f @@ e @@ F1 = f @@ F1) :
                            e C= f :=
  eqrBuildContains {|_; +>e   |} {|_; +>f   |} {|c; eq |} _   := {|+>c   ;_|};
  eqrBuildContains {|_; +>e   |} {|_; t2>>f |} {|c; eq |} _   := {|t2>>c ;_|};
  eqrBuildContains {|_; t1>>e |} {|_; +>f   |} shrinkC    f1C :=! f1C;
  eqrBuildContains {|_; t1>>e |} {|_; t2>>f |} {|c; eq |} f1C := {|c ;_|}.
Next Obligation.
  repeat (program_simpl || simp eqr).
Defined.
Next Obligation.
  repeat (program_simpl || simp eqr).
Defined.
Next Obligation.
  intros.
  handleFinCase0 wildcard1.
  handleFinCase0 wildcard4.
  simp eqr in *; simpl in *.
  apply FS_inj in f1C.
  rewrite <- eq in f1C.
  simp eqr in f1C.
  program_simpl.
Defined.
Next Obligation.
  intros.
  handleFinCase0 c0.
  simp eqr in f1Cond.
  inversion f1Cond.
Defined.
Next Obligation.
  intros.
  handleFinCase0 c0.
  apply False_rect.
  simp eqr in f1Cond.
  inversion f1Cond.
Defined.


(* thus, [erqMaxMapCondition e f] implies [e C= f] *)

Lemma eqrContainsFromEqrMaxMapCondition 
                          {n : nat} (e f : EqR n)
                          (emmc : eqrMaxMapCondition e f) :
                           e C= f.
Proof.
  induction n.
  - rewrite (eqr0Id e). apply idEqrMin.
  - apply eqrBuildContains.
    + apply IHn.
      apply eqrShrinkPreservesEqrMaxMapCondition.
      exact emmc.
    + apply emmc.
Defined.

(* and we have that [eqrToDecEq] reflects containment *)

Lemma eqrToDecEqReflectsContains {n : nat} (e f : EqR n)
                                 (etdeContains : (eqrToDecEq e) c= (eqrToDecEq f)) :
                                 e C= f.
Proof.
  apply eqrContainsFromEqrMaxMapCondition.
  rewrite eqrMaxMapConditionIffEqrToDecEqContains.
  exact etdeContains.
Defined.


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
  - apply erClassMaxNewF1.
  - handleFinCase0 c.
    apply False_rect.
    pose (eqrContainsToEqrMaxMapCondition _ _ cont F1) as mmcF1.
    rewrite eqrToDecEqCompute in mmcF1.
    simp eqr in mmcF1.
    inversion mmcF1.
Defined.

(* decidable predicates on Fin.t n ... *)

Definition DecPFin (n : nat) : Type :=
  { P : Fin.t n -> Prop & forall (x : Fin.t n), {P x} + {~ P x} }.

Definition emptyDPF {n : nat} : DecPFin n.
Proof.
  exists (fun x => False).
  intro. right. exact id.
Defined.

Definition fullDPF {n : nat} : DecPFin n.
Proof.
  exists (fun x => True).
  intro. left. exact I.
Defined.

Obligation Tactic := program_simpl.

Equations dpfMeet {n : nat} (s1 s2 : DecPFin n) : DecPFin n :=
  dpfMeet {| P1 ; decP1 |} {| P2 ; decP2 |} :=
     {| fun x => (P1 x) /\ (P2 x) ; fun x => _ |}.
Next Obligation.
  destruct (decP1 x); destruct (decP2 x).
  - left; split; assumption.
  - right; intros [p1X p2X]. exact (n0 p2X).
  - right; intros [p1X p2X]. exact (n0 p1X).
  - right; intros [p1X p2X]. exact (n0 p1X).
Defined.

Equations dpfJoin {n : nat} (s1 s2 : DecPFin n) : DecPFin n :=
  dpfJoin {| P1 ; decP1 |} {| P2 ; decP2 |} :=
     {| fun x => (P1 x) \/ (P2 x) ; fun x => _ |}.
Next Obligation.
  destruct (decP1 x); destruct (decP2 x).
  - left; left; assumption.
  - left; left; assumption.
  - left; right; assumption.
  - right. intros [p1 | p2].
    + exact (n0 p1).
    + exact (n1 p2).
Defined.

Equations dpfShrink {n : nat} (s : DecPFin (S n)) : DecPFin n :=
  dpfShrink {| P ; decP |} :=
   {| fun x => (P (FS x)) ; fun x => _ |}.

Equations dpfSingle {n : nat} (x : Fin.t n) : DecPFin n :=
  dpfSingle {n:=0} x :=!x ;
  dpfSingle {n:=(S _)} x := {| fun y => y = x ; fun y => _ |}.
Next Obligation.
  destruct (t_eqdec _ y x) as [eq | neq].
  + left. exact eq.
  + right. exact neq.
Defined.

(* classDPF *)

Equations eqrClassDPF {n : nat} (e : EqR n) (x : Fin.t n) : DecPFin n :=
  eqrClassDPF e x := {| fun y => e @@ y = e @@ x ; fun y => _ |}.
Next Obligation.
  destruct (t_eqdec _ (e @@ y) (e @@ x)).
  - left; assumption.
  - right; assumption.
Defined.

(* for a decidable predicate, we either have some x satisfying it or
   a proof that no element satisfies it *)

Equations dpfSomeOrNone {n : nat} (dp : DecPFin n) :
    {x : Fin.t n & dp.1 x } + (forall y, ~ (dp.1 y)) :=
  dpfSomeOrNone {n:=0}      _ := (inr _);
  dpfSomeOrNone {n:=(S _ )} {| P ; decP |} with dpfSomeOrNone (dpfShrink {|P;decP|}) := {
                            | (inl {| x ; pf |})  := (inl {| (FS x); _ |});
                            | (inr pfNone) with decP F1  := {
                              | (left PF1)   := (inl {| F1 ; PF1 |});
                              | (right NPF1) := (inr (fun z => _))
                            }}.
Next Obligation.
  inversion y.
Defined.
Next Obligation.
  dependent induction z.
  + exact NPF1.
  + exact (pfNone z).
Defined.

(* a subset s defines an equivalence relation that
   connects the elements of s *)

Equations eqrFromDPF {n : nat} (s : DecPFin n) : EqR n :=
  eqrFromDPF {n:=0}      _   := {|_ ; #|};
  eqrFromDPF {n:=(S _)} {| P ; decP |}
              with eqrFromDPF (dpfShrink {| P ; decP |}) := {
              | {|_ ; e|}
                with (dpfSomeOrNone (dpfShrink {| P ; decP |})) := {
                | (inl {| x ; _ |}) with decP F1 := {
                  | (left _)  := {| _; (e @v x)>>e |};
                  | (right _) := {| _; +> e |}};
                | (inr _) := {| _; +> e |}}}.

(*
Equations eqrFromDPFShrink {n : nat} (s : DecPFin (S n)) :
   eqrShrink (eqrFromDPF s) = eqrFromDPF (dpfShrink s) :=
  eqrFromDPFShrink s := _.
Next Obligation.
  induction n.
  - simpl. destruct s. program_simpl.
  - ...?

Lemma eqrFromDPFProperty {n : nat} (s : DecPFin n) (x y : Fin.t n) :
     x ~( eqrFromDPF s )~ y <-> x = y \/ ( s.1 x /\ s.1 y).
Proof.
  handleFinCase0 n.
  split.
  - intro xESy.
    unfold eqrFromDPF in xESy.
    unfold dpfSingle, dpfJoin, eqrFromDPF, eqrFromDPF' in wPz.
    simpl in wPz.

*)

(* the smallest equivalence connecting two given elements in Fin.t n *)

Equations eqrPair {n : nat} (x y : Fin.t n) : EqR n :=
  eqrPair x y := eqrFromDPF (dpfJoin (dpfSingle x) (dpfSingle y)).


(* [eqrPair x y] is contained in an equivalence [e] if [x] and [y] are
   related by [e] *)
(* eqrFromDPFProperty is more general... 
Lemma eqrPairContained {n : nat} (x y : Fin.t n) (e : EqR n) :
                           x ~(e)~ y -> (eqrPair x y) C= e.
Proof.
  intro xEy. simp eqr in xEy.
  
*)

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
                dpfSomeOrNone (dpfMeet (eqrClassDPF {| _ ; e1 |} (e1 @^ t1)) 
                                       (eqrClassDPF {| _ ; e2 |} (e2 @^ t2))) := {
                | (inl {|x ; xProp|}) := {|{|_; (e3 @v x)>>e3|}; _|};
                | (inr notXProp)      := {|{|_; +> e3 |}; _ |}
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
  - split; apply eqrBuildContains.
    + exact c1.
    + simp eqr.
    + exact c2.
    + simp eqr.
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
  - split; apply eqrBuildContains.
    + exact c1.
    + simp eqr.
    + exact c2.
    + simp eqr.
  - intros e4 e4In1 e4In2; apply eqrBuildContains.
    + exact (uni (eqrShrink e4) (eqrShrinkPreservesContains _ _ e4In1)
                                (eqrShrinkPreservesContains _ _ e4In2)).
    + assert (e4 @@ F1 = F1) as eq by (apply (eqrContainedInNewF1 _ _ e4In1)).
      rewrite eq; reflexivity.
Defined.
Next Obligation.
  clear eqrMeet.
  split.
  - split; apply eqrBuildContains.
    + exact c1.
    + simp eqr.
    + exact c2.
    + simp eqr.
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
  simp eqr in *.
  split.
  - split; apply eqrBuildContains.
    + exact c1.
    + simp eqr.
      pose ((eqrContainsToEqrMaxMapCondition _ _ c1) x) as eq.
      simp eqr in eq.
      rewrite eq. rewrite H. reflexivity.
    + exact c2.
    + simp eqr.
      pose ((eqrContainsToEqrMaxMapCondition _ _ c2) x) as eq.
      simp eqr in eq.
      rewrite eq. rewrite H0. reflexivity.
  - intros e4 e4In1 e4In2; apply eqrBuildContains.
    + exact (uni (eqrShrink e4) (eqrShrinkPreservesContains _ _ e4In1)
                                (eqrShrinkPreservesContains _ _ e4In2)).
    + destruct e4; dependent destruction e.
      * simp eqr.
      * handleFinCase0 c.
        simp eqr.
        pose ((eqrContainsToEqrMaxMapCondition _ _ e4In1) F1) as eq1.
        simp eqr in eq1. apply FS_inj in eq1.
        rewrite <- H in eq1.
        pose ((eqrContainsToEqrMaxMapCondition _ _ e4In2) F1) as eq2.
        simp eqr in eq2. apply FS_inj in eq2.
        rewrite <- H0 in eq2.
        admit.
Admitted.
Next Obligation.
  admit.
Admitted.





