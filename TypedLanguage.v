
(***************************************************************************
 * Tracing sharing in an imperative pure calculus: typed expressions
          
               Paola Giannini and Tim Richter
 *  
 ***************************************************************************)




Require Import Metatheory.
Require Import SharingRelation.
Require Export Coq.Lists.ListSet.

(** * Syntax *)

(** ** Lexical categories *)

(** Names of variables, fields, methods and classes are atoms (their equality
    is decidable). *)

Definition var := atom.
Definition fname := atom.
Definition cname := atom.
Definition num := atom.


(** The names [this] and [res] are predefined. We simply assume that these
    names exist. The metavaraible [res] denote the result of the evaluation
    of an expression (not part of the source language) *)


(** ** Types and term expressions *)

(** Types for expression results. **)

Inductive ty : Type :=
   | Cl    : cname -> ty
   | TNat  : ty
   | TBool : ty.


(** Types for declaration. Class types may have annotations (in the paper we
    only have [Affine]. **)

Inductive annotation : Type :=
   | Mut    : annotation
   | Affine : annotation.
   

Inductive decTy : Type :=
   | DTNat  : decTy
   | DTBool : decTy
   | DTCl   : cname -> (option annotation) -> decTy.


Fixpoint decTy2ty (dt:decTy) : ty :=
   match dt with
   | DTNat => TNat
   | DTBool => TBool
   | DTCl C _ => (Cl C)
   end.
   
Fixpoint decTy2ann (dt:decTy) : option annotation :=
   match dt with
   | DTNat => None
   | DTBool => None
   | DTCl C an => an
   end.   

   
(** Block annotations: the set of variables possibly sharing with the result
    of the expression. Block annotations are not part of the source language. **)

Definition blAnnotation := list var.  

      
(** The expression forms are variable reference, object creation, method invocation,
    field ccess, fiels update and (possibly annotated) blocks. *)

Inductive exp : Type :=
   | ENum  : nat -> exp
   | ETrue  :  exp
   | EFalse  :  exp
   | EVar  : var -> exp
   | ENew  : cname -> list exp -> exp
   | EFld  : exp -> fname -> exp
   | EUpd  : exp -> fname -> exp -> exp
   | EBlk  : blAnnotation -> list dec ->  exp -> exp

with dec : Type :=
   Dec : decTy -> var -> exp -> dec.
   

(** Some operations on dec: construction and destruction.  *)

Fixpoint toDecs (xs:(list var)) (dts:(list decTy)) (es:(list exp)): (list dec) :=
   match xs,dts,es with
   | nil,nil,nil => nil
   | x::xl,dt::dtl,e::el =>(Dec dt x e)::(toDecs xl dtl el)
   | _,_,_ => nil
   end. 
   
Fixpoint dec_vars (ds:list dec): (list var) :=
   match ds with
   | nil => nil
   | (Dec dt x e)::tl =>x::(dec_vars tl)
   end.

Fixpoint dec_es (ds:list dec): (list exp) :=
   match ds with
   | nil => nil
   | (Dec dt x e)::tl =>e::(dec_es tl)
   end.

(** [split_dec x ds] partitions the declarations in ds in the ones before and
after the declaration of x. 
Namely [split_dec x ds] returns [(ds',dsx)] where if [x] is declared in [ds] then
[ds=ds' dsx] and [dsx=(Dec dt x e) ...], otherwise [ds2=nil]. The function
[split_aux x ds1 ds2] is used to give a tail recursive definition.  *)

Fixpoint split_aux (x:var) ds1 ds2:=
match ds2 with 
| nil => (ds1,ds2)
| (Dec dt y e)::tlds => if (x==y) then (ds1,(Dec dt y e)::ds2) 
                                  else (split_aux x (ds1++((Dec dt y e)::nil)) tlds)
end.

Definition split_dec x ds:=(split_aux x nil ds).                                    

Definition dec_in_ds x ds : bool:=
   let (ds1,ds2):=(split_dec x ds) in
      match ds2 with
      | d::tl => true
      | nil => false  
      end.                                    


(** [free_var e] returns the set of free varaibles of e I had to defined the two 
    internal functions (instead that as mutually recursive) otherwise Coq would 
    complain *)

Fixpoint free_var (e: exp): (set var) :=
let ed := eq_atom_dec in
match e with
|(EVar x) => set_add ed x (@empty_set var)
|(ENew C es) => ((fix free_var_es (es: list exp): (set var) :=
                  match es with
                  | nil => nil
                  | e::tl => (set_union ed (free_var e) (free_var_es tl))
                  end
                 )  es)
|(EFld e1 f) => free_var e1
|(EUpd e1 f e2) => (set_union ed (free_var e1) (free_var e2)) 
|(EBlk ann ds e) =>(set_diff ed 
                      (set_union ed 
                         ((fix free_var_ds (ds: list dec): (set var) :=
                           match ds with
                           | nil => nil
                           | (Dec dt x e)::tl => (set_union ed (free_var e) (free_var_ds tl))
                           end
                          )  ds)
                      (free_var e)) 
                    (dec_vars ds))                   
| _ => @empty_set var 
end.

Fixpoint free_var_es (es: list exp): (set var) :=
match es with
|nil => nil
|e::tl =>(set_union eq_atom_dec (free_var e) (free_var_es tl))
end.



(** ** Environments and class tables *)

(** An [env] declares a number of variables and their types. *)

Definition env := (list (var * decTy)).

Fixpoint toEnv (xs:(list var)) (dts:(list decTy)) : env :=
   match xs,dts with
   | nil,nil => nil
   | x::xl,dt::dtl =>(x,dt)::(toEnv xl dtl)
   | _,_ => nil
   end.
   


Definition args := (list (var * decTy)).
Definition flds := (list (fname * ty)).


(* For the moment we do not have inheritance and methods*)
Definition ctable := (list (cname * flds )).


(** We assume a fixed class table [CT]. *)

Parameter CT : ctable.

(** * Auxiliaries *)

(** ** Field lookup *)

(** [field C f t] holds if a field named [f] with type [t] is defined for class
    [C] in the class hierarchy. *)

Inductive fields : cname -> flds -> Prop :=
| fields_def : forall C fs, 
    binds C fs CT ->
    fields C fs.



Definition field (C : cname) (f : fname) (t : ty) : Prop :=
    exists2 fs, fields C fs & binds f t fs.



(** * Typing *)

(** Help function for computing the annotation of a block. *)
Fixpoint is_in x xs: bool:=
match xs with
| nil => false
| y::tlx => if (x==y) then true else is_in x tlx
end.

Fixpoint inter (xs ys: list atom): list atom:=
match xs with
| nil => nil
| x::tlx => if (is_in x ys) then (x::(inter tlx ys)) else (inter tlx ys) 
end.


(** ** Term expression typing *)

(** [typing E e (t, sh)] holds when expression [e] in environment [E], has type [t], and may 
    produces sharing between variables according to the relation [shRel]. Moreover, the 
    equivalence class of the metavariable [res] in [shRel], contains the variables that may
    be connected to the result of the evaluation of the expression.*)

Inductive typing : forall E, exp -> (ty * (shRel (dom E)) * exp) -> Prop :=
| t_num : forall n E,
    typing E (ENum n) (TNat,(id_shRel (dom E)),(ENum n))
| t_tr : forall E,
    typing E ETrue (TBool,(id_shRel (dom E)),ETrue)
| t_fls : forall E,
    typing E EFalse (TBool,(id_shRel (dom E)),EFalse)
| t_var_aff : forall x E C,
    binds x (DTCl C (Some Affine)) E ->
    typing E (EVar x) ((Cl C),(id_shRel (dom E)),(EVar x))
| t_var : forall x E C,
    binds x (DTCl C None) E ->
    typing E (EVar x) ((Cl C),(add_eq_res (id_shRel (dom E)) x),(EVar x))
| t_fld : forall E e eAn shR C t f,
    typing E e ((Cl C),shR,eAn) ->
    field C f t ->
    typing E (EFld e f) (t,shR,(EFld eAn f))
| t_upd : forall E e0 e1 e0An e1An C t shR0 shR1 f,
    typing E e0 ((Cl C),shR0,e0An) ->
    typing E e1 (t,shR1,e1An) ->
    field C f t ->     
    typing E (EUpd e0 f e1) (t,(add_shr shR0 shR1),(EUpd e0An f e1An)) 
| t_new : forall E C fs es shR esAn,
    fields C fs ->
    par_typing E es (imgs fs) (shR,esAn)->
    typing E (ENew C es) ((Cl C),shR,(ENew C esAn))
| t_blk : forall E E' xs ann dtys es shRs esAn e t shR eAn,
    (NoDup xs) ->
    (E'=(toEnv xs dtys)) ->
    dec_typing (E' ++ E) xs dtys es (shRs,esAn)->
    (typing (E' ++ E) e (t,shR,eAn)) ->
    typing E (EBlk ann (toDecs xs dtys es)  e) 
         (let shRTot := (eq_rect (dom (E' ++ E)) shRel (add_shr shR shRs) _ (sum_dom E' E)) in
          (t, 
           (restrict_res2 (dom E') shRTot),
           (EBlk (inter xs (eq_res shRTot)) 
                 (toDecs xs dtys esAn) eAn)
           )
          )
    
with par_typing : forall E : env, (list exp) -> (list ty) -> (shRel (dom E) * (list exp)) -> Prop :=
| wt_nil : forall E,
    ok E ->
    par_typing E nil nil ((id_shRel (dom E)),nil)
| wt_cons : forall E es e ts t shR shRs esAn eAn,
    par_typing E es ts (shRs,esAn)->
    typing E e (t,shR,eAn) ->
    par_typing E (e::es) (t::ts) ((add_shr shR shRs),(eAn::esAn)) 
    
with dec_typing : forall E, (list var) -> (list decTy) -> (list exp) -> (shRel (dom E) * (list exp)) -> Prop :=
| dec_nil : forall E,
    dec_typing E nil nil nil ((id_shRel (dom E)),nil)
| dec_cons : forall E x xs dt dts e es shR shRs esAn eAn, 
    dec_typing E xs dts es (shRs,esAn)->
    typing E e ((decTy2ty dt),shR,eAn) ->
    ((decTy2ann dt)=(Some Affine) -> (capsule shR) ) ->
    dec_typing E (x::xs) (dt::dts) (e::es) ((add_shr (rem_res (add_eq_res shR x)) shRs),(eAn::esAn)).
            


