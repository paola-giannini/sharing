(***************************************************************************
 * Tracing sharing in an imperative pure calculus: garbage elimination
 *  
 ***************************************************************************)


From Equations Require Import Equations.
Set Equations Transparent.
Unset Equations WithK.
Require Import Equations.Subterm.
Require Import PeanoNat.
Require Import NatMisc.
Require Import Fin.
Require Import Metatheory.
Require Import TypedLanguageSimpl.
Require Import List.

(* Require Import TestConnectedP. *)


(*
  First define the predicate [connectedDecs] such that:
      [connectedDecs ds e] if [(EBlk ann ds e)] does not
      contain unreachable local variables
*)
(* [connectedVar ds xs x] asserts that the variable [x] is connected
   to [xs] via the definitions [ds], meaning that either [x] in [xs] 
   or there is a declaration [Dec dt y e] in [ds] such that
   [connectedVar ds xs y] and [x] is free variables of [e] 
*)

Inductive connectedVar: (list dec) -> (list var) -> var -> Prop :=
  | is_def      : forall (ds : list dec) 
                         (xs  : list var) 
                         (x   : var),
                         (In x xs) -> 
                         (connectedVar ds xs x)
  | is_free_def : forall (ds : list dec) 
                         (xs  : list var)
                         (x y : var)
                         (dt : decTy)
                         (e   : exp),
                         (* if there is a declaration [Dec dt x e] in [ds]*)
                         (In (Dec dt x e) ds) -> 
                         (* such that [y] is in the free variables of [e] *)
                         (In y (free_var e)) ->
                         (* and [x] is connected to [xs] via [ds]*)
                         (connectedVar ds xs x) ->
                         (* then [y] is connected to [xs] via [ds] *)
                         (connectedVar ds xs y).


(* we have to show decidability of connected 
Lemma connectedDecidable (dvs : list dec) (xs : list var) (x: var)
      {connectedVar dvs xs x} + {~(connectedVar dvs xs x)}.
Proof.
  (* we have decidability of In, so first split by
    In x xs *)
  induction (In_atom_list_dec x xs).
  - left. exact (is_def dvs xs x a).
  - admit. (* won't work ... *)
Admitted.
*)

(* [connectedDecs ds e] asserts that for all [Dec dt x ex] in [ds]
   [x] is connected to the free variables of [e] via the 
   definitions on [ds] 
*)

Inductive connectedDecs:(list dec) -> (list var) -> Prop :=
  | is_conn : forall  (ds : list dec)
              (x: var)
              (xs  : list var),
              (ok_decs ds) ->
              (In x (dec_vars ds) ) -> 
              (connectedVar ds xs x) ->
              (connectedDecs ds xs).

(* [noGarbageBlock e] asserts that [e] is a block [(EBlk ann decs eb)] 
   and all the variable declared in [decs] are connected to the result of the
   block
*)
Inductive noGarbage: exp -> Prop :=
  | no_garbage : forall (ann: blAnnotation)
              (eb: exp)
              (ds  : list dec),
              (connectedDecs ds (free_var eb) ) -> 
              (noGarbage (EBlk ann ds eb)).


Fixpoint dec_FVes (ds:list dec): list (var * (list var)) :=
   match ds with
   | nil              => nil
   | (Dec dt x e)::tl => (x,(free_var e))::(dec_FVes tl)
   end.



Instance wf_lexprod_nat : WellFounded (lexprod nat nat lt lt) := 
         wellfounded_lexprod nat nat lt lt lt_wf lt_wf.


Equations removeNth {A : Type} {n : nat}
                   (x : Fin.t (S n)) (v : Vector.t A (S n)) : Vector.t
A n :=
 removeNth {n:=0}     _      _  := Vector.nil;
 removeNth {n:=(S _)} F1     vs := Vector.tl vs;
 removeNth {n:=(S _)} (FS x) vs := Vector.cons (Vector.hd vs) (removeNth x (Vector.tl vs)).

Obligation Tactic := idtac.

Equations connected' (dl n : nat) 
                     (ds : Vector.t (var * (list var)) dl) 
                     (Y : list var) : (list (var * list var)) :=
  connected' dl n ds Y by rec (dl, n) (lexprod nat nat lt lt) :=
  connected' 0  _ _ _ := [];
  connected' _ 0 _ _  := [];
  connected' (S dl) (S n) ds Y with (leDicho n dl) := {
                 | (inr dlLtn) := connected' (S dl) (S dl) ds Y;
                 | (inl nLeDl (* n <= dl *))
           with (List.in_dec eq_atom_dec (fst (Vector.nth_order ds (leNS nLeDl))) Y) := {
                 | (left  inY ) := 
                    List.cons (Vector.nth_order ds (leNS nLeDl))
                       (connected' dl dl (removeNth (Fin.of_nat_lt (leNS nLeDl)) ds)
                                         ((snd (Vector.nth_order ds (leNS nLeDl)) ++ Y))) ;
                 | (right nInY) :=
                              (connected' (S dl) n ds Y) }}.
Next Obligation.
  constructor 2.
  apply leNS.
  exact dlLtn.
Defined.


Definition connected (ds : list (var * (list var))) (Y : list var) : list var :=
  (dom (connected' (length ds) (length ds) (Vector.of_list ds) Y)).



Fixpoint split_decs (ds:list dec)(X : list var) {struct ds}:((list dec)*(list dec)) :=
  let Y:= ( connected (dec_FVes ds) X) in
   match ds with
   | nil              => (nil,nil)
   | (Dec dt x e)::tl => 
   (let (conn_decs,garb_decs):=(split_decs tl X) in
      (if (is_in x Y) then ((Dec dt x e)::conn_decs,garb_decs)
      else (conn_decs,(Dec dt x e)::garb_decs)
      )
      )
   end.

  
  

Definition remove_Garbage e:=
  match e with
   | (EBlk ann ds eb) => 
         (let (ds1,ds2):=(split_decs ds (free_var eb))
          in
          (EBlk ann ds1 eb)
         )
   | _ => e
   end.

Lemma split_dec_Ok:
   (forall ds X x ds1 ds2,
     (split_decs ds X =(ds1,ds2)) -> (
       ((In x (dec_vars ds1))->(connectedVar ds X x) )
        /\ 
        
       ((In x (dec_vars ds2))->~(connectedVar ds X x) )
       )                       
   ).
Proof.
Admitted.

Theorem garbage_elim:
   (forall e ann ds eb,
     (e=(EBlk ann ds eb))->(noGarbage (remove_Garbage e))
   ).
Proof.
Admitted.
