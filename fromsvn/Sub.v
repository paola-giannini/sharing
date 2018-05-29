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

(* [Sub n] contains the subsets of Fin.t n *)

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
singleSub {n:=0}      x     :=! x;
singleSub {n:=(S _)}  F1    := SNew emptySub;
singleSub {n:=(S _)} (FS y) := SOld (singleSub y).

Equations subComplement {n : nat} (s : Sub n) : Sub n :=
subComplement SEmpty    := SEmpty;
subComplement (SNew t)  := SOld (subComplement t);
subComplement (SOld t)  := SNew (subComplement t).

Inductive InSub : forall {n : nat}, Sub n -> Fin.t n -> Prop :=
   | NewIn    : forall {n : nat} (s : Sub n), InSub (SNew s) F1
   | OldInOld : forall {n : nat} {s : Sub n} {x : Fin.t n} (xInS : InSub s x),
                                           InSub (SOld s) (FS x)
   | OldInNew : forall {n : nat} {s : Sub n} {x : Fin.t n} (xInS : InSub s x),
                                           InSub (SNew s) (FS x).


Equations(noind) decInSub {n : nat} (s : Sub n) (x : Fin.t n) : 
                   decidable (InSub s x) :=
decInSub {n:=0}  _  x  :=! x;
decInSub {n:=(S _)} (SNew s)  F1    := or_introl (NewIn s);
decInSub {n:=(S _)} (SNew s) (FS x) with decInSub s x := {
                    | (or_introl xIns) := (or_introl (OldInNew xIns));
                    | (or_intror xNis) := (or_intror _)};
decInSub {n:=(S _)} (SOld s)  F1    := or_intror _;
decInSub {n:=(S _)} (SOld s) (FS x) with decInSub s x := {
                    | (or_introl xIns) := (or_introl (OldInOld xIns));
                    | (or_intror xNis) := (or_intror _)}.
Next Obligation.
  intro.
  apply xNis.
  inversion H.
  apply sigmaNat in H2; apply sigmaNat in H3.
  rewrite <- H2; rewrite <- H3.
  exact xInS.
Defined.
Next Obligation.
  intro. inversion H.
Defined.
Next Obligation.
  intro.
  apply xNis.
  inversion H.
  apply sigmaNat in H2; apply sigmaNat in H3.
  rewrite <- H2; rewrite <- H3.
  exact xInS.
Defined.





(*

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

*)

