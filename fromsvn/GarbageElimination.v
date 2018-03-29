(***************************************************************************
 * Tracing sharing in an imperative pure calculus: garbage elimination
 *  
 ***************************************************************************)

Require Import List.

Require Import TypedLanguage.

Require Import Metatheory.

(*
Inductive connected: (list dec) -> (list var) -> Prop:=
   | is_def      : forall dvs xs,
                   (incl (dec_vars dvs) xs) ->  
                   (connected dvs xs)
   | is_free_def : forall dvs dvs1 dvs2 xs,
                   ((dvs = dvs1++dvs2) /\ (connected dvs1 xs) /\ 
                     (connected dvs2 (free_var_es (dec_es dvs1)))) -> 
                   (connected dvs xs).
*)

Inductive decNoTy : Set :=
  DecNoTy : var -> exp -> decNoTy.

Fixpoint decTodecNoTy (d : dec) : decNoTy :=
  match d with
  | Dec _ x e => DecNoTy x e
  end.

Definition decTodecNoTys : (list dec) -> (list decNoTy) :=
  List.map decTodecNoTy.

(* doesn't work ... 
   because in_split maps to (ex ...) which is a Prop!
Definition removeOccuring (a : atom) (l : list atom) (aInL : In a l) : list atom :=
  match (in_split a l aInL) with
  | @ex_intro _ _ l1 (@ex_intro _ _ l2 _) => l1 ++ l2
  end.
*)

Inductive connected: (list dec) -> (list var) -> var -> Prop :=
  | is_def      : forall (dvs : list dec) 
                         (xs  : list var) 
                         (x   : var),
                         (In x xs) -> connected dvs xs x
  | is_free_def : forall (dvs : list dec) 
                         (xs  : list var)
                         (x y : var)
                         (e   : exp)
                         (dv  : dec),
                         (* dv initialises x to e *)
                         (decTodecNoTy dv = DecNoTy x e) ->
                         (* dv occurs in dvs *)
                         (In dv dvs) -> 
                         (* y is in the free variables of e *)
                         (In y (free_var e)) ->
                         (* y is connected *)
                         (connected dvs xs y) ->
                         (* then x is connected *)
                         (connected dvs xs x).


(* we have to show decidability of connected *)
Lemma connectedDecidable (dvs : list dec) (xs : list var) (x : var):
      {connected dvs xs x} + {~(connected dvs xs x)}.
Proof.
  (* we have decidability of In, so first split by
    In x xs *)
  induction (In_atom_list_dec x xs).
  - left. exact (is_def dvs xs x a).
  - admit. (* won't work ... *)
Admitted.



