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

(* ... unfortunately, [+>] and [>>]  cannot be used in patterns 
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
   of the map sending an element to its equivalence class. *)

Equations erMap {n c : nat} (e : ER n c) : Vector.t (Fin.t c) n :=
  erMap  #          := [];
  erMap (ERNew e)   := F1 :: (map FS (erMap e));
  erMap (ERPut t e) := t  ::         (erMap e).

Notation "e '@v' t" := (Vector.nth (erMap e) t) 
                       (at level 61, right associativity).

Obligation Tactic := try repeat (rewrite nthMapLemma || program_simpl).

(* computation lemmata for [@v] *)

Equations erMapNewF1 {n c : nat} (e : ER n c) :
                     (+> e) @v F1 = F1 :=
  erMapNewF1 _ := _.

Equations erMapNewFS {n c : nat} (e : ER n c) (y : Fin.t n) :
                     (ERNew e) @v (FS y) = FS (e @v y) :=
  erMapNewFS _ _ := _.

Equations erMapPutF1 {n c : nat} (e : ER n c) (t : Fin.t c) :
                     (t >> e) @v F1 = t :=
  erMapPutF1 _ _ := _.

Equations erMapPutFS {n c : nat} (e : ER n c)
                     (t : Fin.t c) (y : Fin.t n) :
                     (t >> e) @v (FS y) = (e @v y) :=
  erMapPutFS _ _ _ := _.

Ltac erRewrite1 := 
   (rewrite erMapNewF1 in * ||
    rewrite erMapNewFS in * ||
    rewrite erMapPutF1 in * ||
    rewrite erMapPutFS in *).

Ltac erRewrites1 := try repeat erRewrite1.

Ltac erSpecial := (rewrite nthMapLemma in *|| apply (f_equal FS)).

Ltac erSimpl1 := try repeat 
    (erRewrite1    ||
     erSpecial     ||
     program_simpl).

Obligation Tactic := erSimpl1.

(** properties of [@v] **)

(* erMap of idER is the identity *)

Equations(noind) idERId {n : nat} (x : Fin.t n) : idER @v x = x :=
  idERId  F1     := _;
  idERId (FS x)  with (idERId x) := { | IH := _}.


(** erSection **)

(* [erSection e] maps each class to its largest representative *)

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

Equations erSectionNewFS {n c : nat} (e : ER n c) (y : Fin.t c) :
                         (+>e) @^ (FS y) = FS (e @^ y) :=
  erSectionNewFS _ _ := _.

Equations erSectionPut {n c : nat} (e : ER n c) (t x : Fin.t c) :
                       (t >> e) @^ x = FS (e @^ x) :=
  erSectionPut _ _ _ := _.

Ltac erRewrite2 :=
  (rewrite erSectionNewF1 in * ||
   rewrite erSectionNewFS in * ||
   rewrite erSectionPut   in * ||
   erRewrite1).

Ltac erRewrites2 := try repeat erRewrite2.

Ltac erSimpl2 := try repeat
    (erRewrite2 || erSpecial  || program_simpl).

Obligation Tactic := erSimpl2.

(* [erSection e] is a section of [erMap e] *)

Lemma erSectionIsSection {n c : nat} (e : ER n c) (y : Fin.t c) :
                          e @v e @^ y = y.
Proof. induction e; dependent destruction y; erSimpl2. Defined.

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

Notation "e '@>' x" := (Vector.nth (erClassMin e) x) 
                       (at level 61, right associativity).

(* [e @>] is [e @v] followed by [e @^] *)

Equations erClassMinExpand {n c : nat} (e : ER n c) (x : Fin.t n) :
                           e @> x = e @^ e @v x :=
  erClassMinExpand _ _ := _.

(* [e @>] is idempotent *)

Lemma erClassMinIsIdempotent {n c : nat} (e : ER n c) (x : Fin.t n) :
                              e @> e @> x = e @> x.
Proof.
  repeat rewrite erClassMinExpand.
  rewrite erSectionIsSection.
  reflexivity.
Defined.

(* computation lemmata for [@>] *)

Ltac erRewrite3 :=
   (rewrite erClassMinIsIdempotent in * ||
    rewrite erClassMinExpand       in * ||
    rewrite erSectionIsSection     in * ||
    rewrite erSectionIsInjective   in * ||
    erRewrite2).

Ltac erRewrites3 := try repeat erRewrite3.

Ltac erSimpl3 := try repeat 
   (erRewrite3 || erSpecial || program_simpl).

Obligation Tactic := erSimpl3.

Equations erClassMinNewF1 {n c : nat} (e : ER n c) :
                          (+>e) @> F1 = F1 :=
  erClassMinNewF1 _ := _.

Equations erClassMinNewFS {n c : nat} (e : ER n c) (y : Fin.t n) :
                          (+>e) @> (FS y) = FS ( e @> y ) :=
  erClassMinNewFS _ _ := _.

Equations erClassMinPutF1 {n c : nat} (e : ER n c) (t : Fin.t c) :
                          (t >> e) @> F1 = FS (e @^ t) :=
  erClassMinPutF1 _ _ := _.

Equations erClassMinPutFS {n c : nat} (e : ER n c) (t : Fin.t c) (x : Fin.t n) :
                          (t >> e) @> (FS x) = FS (e @> x) :=
  erClassMinPutFS _ _ _ := _.

Ltac erRewrite4 :=
  (rewrite erClassMinNewF1  in * ||
   rewrite erClassMinNewFS  in * ||
   rewrite erClassMinPutF1  in * ||
   rewrite erClassMinPutFS  in * ||
   erRewrite3).

Ltac erRewrites4 := try repeat erRewrite4.

Ltac erSimpl4 := try repeat
  (erRewrite4 || erSpecial || program_simpl).

Obligation Tactic := erSimpl4.

(** [eqrClassMin] **)

(* the result type of [erClassMin e] is not dependent on c, so we can define *)

Definition eqrClassMin {n : nat} (e : EqR n) :
                        Vector.t (Fin.t n) n :=
  erClassMin (e.2).

Notation "e '@@' x" := (Vector.nth (eqrClassMin e) x)
                       (at level 61, right associativity).

(* trivial computation lemma for [@@] *)

Equations eqrClassMinCompute {n c : nat} (e : ER n c) (x : Fin.t n) :
                             {| c ; e |} @@ x = e @> x :=
  eqrClassMinCompute _ _ := _.

(* [e @@] is idempotent *)

Equations eqrClassMinIsIdempotent {n : nat} (e : EqR n) (x : Fin.t n) :
                                  e @@ e @@ x = e @@ x :=
  eqrClassMinIsIdempotent _ _ := _.

Ltac erRewrite5 :=
  (rewrite eqrClassMinIsIdempotent  ||
   rewrite eqrClassMinCompute       ||
   erRewrite4).

Ltac erRewrites5 := try repeat erRewrite5.

Ltac erSimpl5 := try repeat
  (erRewrite5 || erSpecial || program_simpl).

Obligation Tactic := erSimpl5.


(** the decidable equivalence relation on [Fin.t n] defined by [e : EqR n] *)

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

(* postcomposing with [allER] maps to [allER] *)

Definition allERRight {n d : nat} (e : ER (S n) (S d)) :
                       e ** allER = allER.
Proof. apply ern1AllER. Defined.

(* Obligation Tactic := try repeat (erRewrites5 || program_simpl). *)
Obligation Tactic := erSimpl5.

Ltac handleFinCase0 n := try (destruct n; [> apply Fin.case0; trivial | idtac]).

Equations(noind) erMapCompose {n m l : nat} (e1 : ER n m) (e2 : ER m l) 
                              (x : Fin.t n) :
                              (e1 ** e2) @v x = e2 @v (e1 @v x) :=
  erMapCompose {n:=0}      #            #             x          :=! x;
  erMapCompose {n:=(S _)} (ERNew e1)   (ERNew e2)     F1         := _;
  erMapCompose {n:=(S _)} (ERNew e1)   (ERNew e2)    (FS y) with erMapCompose e1 e2 y := {
                                                            | IH := _};
  erMapCompose {n:=(S _)} (ERNew e1)   (ERPut t2 e2)  F1         := _;
  erMapCompose {n:=(S _)} (ERNew e1)   (ERPut t2 e2) (FS y) with erMapCompose e1 e2 y := {
                                                            | IH := _};
  erMapCompose {n:=(S _)} (ERPut t1 e1) e2            F1         := _;
  erMapCompose {n:=(S _)} (ERPut t1 e1) e2           (FS y) with erMapCompose e1 e2 y := {
                                                            | IH := _}.
(* above typechecks, but takes way too long ... have to adjust tactics *)


(* [erSection] of [e1 ** e2] is composition of [erSection]s.
   Note the order! *)

Equations(noind) erSectionCompose {n m l : nat} (e1 : ER n m) (e2 : ER m l) 
                                  (x : Fin.t l) :
                                  (e1 ** e2) @^ x = e1 @^ (e2 @^ x) :=
  erSectionCompose {n:=0}     #           #            x                  :=! x;
  erSectionCompose {n:=(S _)} (ERNew e1)  (ERNew e2)    F1                 := _;
  erSectionCompose {n:=(S _)} (ERNew e1)  (ERNew e2)   (FS y) with erSectionCompose e1 e2 y := {
                                                         | IH := _ };
  erSectionCompose {n:=(S _)} (ERNew e1)  (ERPut _ e2)  F1               := _;
  erSectionCompose {n:=(S _)} (ERNew e1)  (ERPut _ e2) (FS y) with erSectionCompose e1 e2 (FS y) := {
                                                         | IH := _ };
  erSectionCompose {n:=(S _)} (ERPut _ e1) e2        x        with erSectionCompose e1 e2 x := {
                                                         | IH := _ }.


Ltac erRewrite6 :=
  (rewrite idERLeft1        ||
   rewrite idERRight1       ||
   rewrite allERRight       ||
   rewrite erMapCompose     ||
   rewrite erSectionCompose ||
   erRewrite5).

Ltac erRewrites6 := try repeat erRewrite6.

Ltac erSimpl6 := try repeat 
  (erRewrite6 || erSpecial || program_simpl).

Ltac erSimpl6In H :=
   generalize H; erSimpl6; clear H; intro H.

Obligation Tactic := erSimpl6.

(* [**] is associative *)

Lemma erComposeAssociative {n m l k : nat}
                           (e1 : ER n m) (e2 : ER m l) (e3 : ER l k) :
                           (e1 ** e2) ** e3 = e1 ** e2 ** e3.
Proof.
  funelim (e1 ** e2).
  - funelim (# ** e3). reflexivity.
  - funelim ((+> (e ** e0)) ** e3); erSimpl6; rewrite H1; trivial.
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
  destruct e as [c e], f as [d f], p as [g eq]; simpl in *.
  rewrite eqrToDecEqContainsRewrite.
  intros x y.
  repeat rewrite <- eq.
  erSimpl6.
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

Lemma eqrContainsToEqrMinMapCondition 
                          {n : nat} (e f : EqR n) (cont: e C= f) :
                          eqrMinMapCondition e f.
Proof.
  intro x.
  handleFinCase0 n.
  rewrite eqrToDecEqCompute.
  destruct e as [c1 e], f as [c3 f], cont as [c eq]; simpl in *.
  rewrite <- eq.
  erSimpl6.
Defined.

(* that [eqrMinMapCondition e f] implies [e C= f] is a little more difficult *)

(* Restrict equivalence on [n+1] elements to the first [n] elements
   Just take the constructor argument of the 2nd component and repack it.
   Needed only to shorten statements. *)

Equations eqrShrink {n : nat} (e : EqR (S n)) :
                    EqR n :=
  eqrShrink {|_ ;   +> e |} := {|_ ; e |};
  eqrShrink {|_ ; _ >> e |} := {|_ ; e |}.

(* on the higher elements, [eqrShrink e] does "essentailly the same" as [e] *)

Lemma eqrShrinkClassMin {n : nat} (e : EqR (S n)) (x : Fin.t n) :
                        FS ((eqrShrink e) @@ x) = e @@ (FS x).
Proof.
  destruct e as [k e].
  dependent induction e.
  - rewrite eqrShrink_equation_1. apply eq_sym. erSimpl6.
  - rewrite eqrShrink_equation_2. apply eq_sym. erSimpl6.
Defined.

Lemma eqrShrinkPreservesEqrMinMapCondition 
                        {n : nat} (e f : EqR (S n)) 
                        (emms : eqrMinMapCondition e f) :
                        eqrMinMapCondition (eqrShrink e) (eqrShrink f).
Proof.
  unfold eqrMinMapCondition, eqrToDecEq in *; simpl in *;
  unfold pullbackRelation in *. (* lowlevel rewrites really necessary ?? *)
  intro x.
  apply FS_inj.
  repeat rewrite eqrShrinkClassMin.
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
   [eqrMinMapCondition e f F1]  *)

Equations eqrBuildContains {n : nat} (e f :  EqR (S n))
                           (shrinkCond : (eqrShrink e) C= (eqrShrink f))
                           (f1Cond     : f @@ e @@ F1 = f @@ F1) :
                            e C= f :=
  eqrBuildContains {|_; +>e   |} {|_; +>f   |} {|c; eq |} _   := {|+>c   ;_|};
  eqrBuildContains {|_; +>e   |} {|_; t2>>f |} {|c; eq |} _   := {|t2>>c ;_|};
  eqrBuildContains {|_; t1>>e |} {|_; +>f   |} shrinkC    f1C :=! f1C;
  eqrBuildContains {|_; t1>>e |} {|_; t2>>f |} {|c; eq |} f1C := {|c ;_|}.
Next Obligation.
  handleFinCase0 wildcard1.
  cut (c @v t1 = t2).
  - intro eq. rewrite eq. reflexivity.
  - (* to be looked at again ... *)
    generalize f1C. erSimpl6. clear f1C0.
    repeat rewrite nthMapLemma in f1C.
    generalize f1C. erSimpl6.
    pose (sigmaNat H0) as eq.
    repeat (rewrite erSectionIsInjective in eq).
    exact eq.
Defined.
Next Obligation.
  clear shrinkCond.
  apply False_rect.
  repeat (rewrite nthMapLemma in f1Cond|| simpl in f1Cond).
  inversion f1Cond.
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

Lemma eqrContainedInNewF1 {n c1 : nat} (e : EqR (S n)) (e1 : ER n c1) 
           (cont : e C= {|_; +> e1|}) :
            e @@ F1 = F1.
Proof.
  destruct e as [c e].
  dependent destruction e.
  - apply erClassMinNewF1.
  - handleFinCase0 c.
    apply False_rect.
    pose (eqrContainsToEqrMinMapCondition _ _ cont F1) as mmcF1.
    rewrite eqrToDecEqCompute in mmcF1.
    erSimpl6In mmcF1.
Defined.

Obligation Tactic := erSimpl6.

(*
Equations eqrMeet (n : nat) (e1 e2 : EqR n) :
                  { e : EqR n & ( (e C= e1) * (e C= e2) * 
                                   forall e' : EqR n,
                                          e' C= e1 -> e' C= e2 -> 
                                          e' C= e )%type } :=
eqrMeet n e1 e2 by rec n lt :=
eqrMeet 0     {|_;#     |} {|_; #    |} := {| {|0;#|} ; _ |};
eqrMeet (S _) {|_;+>e1  |} {|_; +>e2 |}
 with (eqrMeet _ {|_;e1|} {|_;e2|}) := { | {| {| d3 ; e3 |} ; (c1,c2,uni) |} :=
                                           {| {|_; +> e3 |}; _ |}  };
eqrMeet (S _) {|_;t1>>e1|} {|_; +>e2 |}  with (eqrMeet _ {|_;e1|} {|_;e2|}) := {
                                         | {| {| d3 ; e3 |} ; (c1,c2,uni) |} :=
                                           {| {|_; +> e3 |}; _ |}  };
eqrMeet (S _) {|_;+>e1  |} {|_;t2>>e2|} with (eqrMeet _ {|_;e1|} {|_;e2|}) := {
                                         | {| {| d3 ; e3 |} ; (c1,c2,uni) |} :=
                                           {| {|_; +> e3 |}; _ |}  };
eqrMeet (S _) {|_;t1>>e1|} {|_;t2>>e2|} with (eqrMeet _ {|_;e1|} {|_;e2|}) := {
                                         | {| {| d3 ; e3 |} ; (c1,c2,uni) |} :=_}.
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







