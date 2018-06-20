Require Import NatMisc.
Require Import NotationsMisc.
From Equations Require Import Equations.
Set Equations Transparent.
Unset Equations WithK.

(* transport is just eq_rect with adapted parameter ordering and implicity *)

Definition transport {A : Type} {x y : A} 
                     (eq : x = y) (B : A -> Type) (bx : B x) : B y :=
  eq_rect x B bx y eq.

Notation "eq '*^' B" := (transport eq B) (at level 1).

(* paths "over" paths *)

Definition eq_over {A : Type} {x y : A} (eq : x = y)
                   (B : A -> Type) (ox : B x) (oy : B y) : Type :=
  eq *^ B ox = oy.

(* TODO think about better notation *)

Notation "ox '=^' B '=(' eq ')=' oy" := (eq_over eq B ox oy) (at level 5).


(* equality in sigma type induces equality in the base. *)

Equations sigmaEq1 {A : Type} {B : A -> Type} 
                   {x y : { a : A & B a}} (eq : x = y) : x.1 = y.1 :=
sigmaEq1 eq_refl := eq_refl.

Notation "p '=.1'" := (sigmaEq1 p) (at level 1).

(* and equality in the fibers "over" the base equality *)

Equations sigmaEq2 {A : Type} {B : A -> Type}
                   {x y : { a : A & B a}} (eq : x = y) :
                   x.2 =^ B =( eq=.1 )=  y.2 :=
sigmaEq2 eq_refl := eq_refl.

Notation "p '=.2'" := (sigmaEq2 p) (at level 1).


(* Since "eq_refl*^B" is the identity for any B, "=^ B =( eq_refl )="  is just "=".
   If the base has UIP, and eq : {| a ; x |} = {| a ; y |}, we get x = y.
   We need this for base nat:  *)

Equations sigmaNat {B : nat -> Type} {n : nat} {x y : B n}
                   (eq : {| n ; x |} = {| n ; y |}) : x = y :=
sigmaNat eq := _.
Next Obligation.
  pose (eq=.2) as eq'; simpl in eq'.
  assert (eq=.1 = eq_refl) as eqEqRefl by (apply uipNat).
  rewrite eqEqRefl in eq'.
  exact eq'.
Defined.

(* and for base (nat,nat)  (in curried form...) *)

Equations sigmaNat2 {B : nat -> nat -> Type} {n c : nat} {x y : B n c}
                    (eq : (existT (fun n => { c : nat & B n c }) n {| c ; x |}) = 
                          (existT (fun n => { c : nat & B n c }) n {| c ; y |})) : x = y :=
sigmaNat2 eq := _.
Next Obligation.
  apply sigmaNat.
  apply (@sigmaNat (fun n => { c : nat & B n c})).
  exact eq.
Defined.

(* ... *)

Equations sigmaEqCompute {A : Type} {B : A -> Type}
                         (x : {a : A & B a}) : {| x.1 ; x.2 |} = x :=
  sigmaEqCompute {| x1 ; x2 |} := eq_refl.




