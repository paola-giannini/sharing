(***************************************************************************
 * Tracing sharing in an imperative pure calculus: evaluation
 *  
 ***************************************************************************)

Require Import List.

Require Import TypedLanguageSimpl.
Require Import Metatheory.
Require Import Connected.
Require Import Coq.Bool.Bool.

(* Values *)

(** [value exp] holds if [exp] is a value, 
           val::= x | n | tr | fls | new C(xs) | {X dvs x}
   [ev_dec dvs] holds 
   if the declarations in [dvs] are all evaluated 
          dv::= C x=new C(xs)
 *)
Inductive is_var: exp -> Prop := 
   | var_x : forall x, is_var (EVar x).


Inductive value : exp -> Prop :=
   | val_x   : forall x, value (EVar x)
   | val_num : forall n, value (ENum n)
   | val_tr  : value ETrue
   | val_fls : value EFalse
   | val_new : forall C xs,
               (value (ENew C xs))
   | val_blk : forall ann dv dvs x,
               (Forall ev_dec (dv::dvs)) ->
               (is_var x) ->
               (noGarbage (EBlk ann (dv::dvs)  x))->
               (value (EBlk ann (dv::dvs)  x))

with
ev_dec : dec -> Prop :=
   |val_dec : forall C x xs,
               ev_dec   (Dec (DTCl C None) x (ENew C xs)).



Definition Value : Type := { v : exp | value v }. 

(** Substitution of one variable with another: alpha rename and alpha congruence *)

Definition rename := (list (var * var)).

Fixpoint rename_var (rn:rename) (x:var)  : var :=
  match rn with
  | nil        => x
  | (z,y)::tlr => ( if (z==x) then y else (rename_var tlr x) )
  end.

Fixpoint rename_vars (rn:rename) (xs:list var)  : list var :=
  match xs with
  | nil    => nil
  | x::tlx => (rename_var rn x)::(rename_vars rn tlx)
  end.


Definition rename_ann (rn:rename) (ann:blAnnotation): blAnnotation := (rename_vars rn ann).                    

Fixpoint rename_exp (rn:rename) (e:exp) {struct e}: exp :=
  match e with
  | (EVar x)        => (EVar (rename_var rn x)) 
  | (ENew C xs)     => (ENew C (rename_vars rn xs))
  | (EFld x f)     => (EFld (rename_var rn x) f) 
  | (EUpd x1 f x2)  => (EUpd (rename_var rn x1) f (rename_var rn x2)) 
  | (EBlk a ds e)   => (EBlk (rename_ann rn a) 
                        ((fix rename_ds (ds:list dec) : (list dec):=
                          match ds with
                          | nil => nil
                          | (Dec dt z ez)::tl => (Dec dt z (rename_exp rn ez))::(rename_ds tl)
                          end
                         ) ds)
                         (rename_exp rn e))
  | ek              => ek
  end.


Fixpoint rename_ds (rn:rename) (ds:list dec) : (list dec):=
  match ds with
  | nil              => nil
  | (Dec dt z e)::tl => (Dec dt z (rename_exp rn e))::(rename_ds rn tl)
  end.

Fixpoint alpha_rename_ds (x:var) (y:var) (ds:list dec) : list dec :=
  match ds with
  | nil                 => nil
  | (Dec dt z ez)::tlds => 
        if (z==x)  then
          (Dec dt y (rename_exp ((x,y)::nil) ez))::(alpha_rename_ds x y tlds)
        else  (Dec dt z ez)::(alpha_rename_ds x y tlds)
end.


Inductive alpha_cong: exp -> exp -> Prop:=
 | cong_id  : forall e:exp,  alpha_cong e e
 | cong_blk : forall ann ds e dt x ds1 ds2 ds3 ex y,
               (split_dec x ds)=(ds1,ds2) ->
               ds2 = (Dec dt x ex)::ds3 ->
               (not (In y (dec_vars ds))) ->
               alpha_cong (EBlk ann ds  e) 
                 (EBlk (rename_ann ((x,y)::nil) ann) 
                       (alpha_rename_ds x y ds)
                       (rename_exp ((x,y)::nil) e))
  | cong_trans : forall e1 e2 e3,
                 (alpha_cong e1 e2) ->
                 (alpha_cong e2 e3) ->
                 (alpha_cong e1 e3)
  | cong_sym : forall e1 e2,
               (alpha_cong e1 e2) ->
               (alpha_cong e2 e1)

with alpha_cong_es: (list exp) -> (list exp) -> Prop:=
  | cong_nil  : alpha_cong_es nil nil
  | cong_cons : forall e e' es es',
                alpha_cong e e' ->
                alpha_cong_es es es' ->
                alpha_cong_es (e::es) (e'::es').


(** [fresh_vars n ys], returns a list of n different fresh variables such that none
  of them is in [ys] *) 

Definition fresh_var (xs:list var) : var :=(proj1_sig (atom_fresh_for_list xs)). 


Fixpoint fresh_vars (n:nat)  (ys:list var) : list var :=
  match n with
  | 0     => nil
  | (S m) => (let z:=(proj1_sig (atom_fresh_for_list ys)) in
                z::(fresh_vars m (z::ys)))
end.


Definition zip : list var -> list var -> list (var * var) := @combine var var.

Fixpoint alpha_renames_ds (rn:rename) (ds:list dec): list dec :=
  match rn with
  | nil        => ds
  | (x,y)::tlr => alpha_renames_ds tlr (alpha_rename_ds x y ds)
  end.




Definition mk_block_with_def (x:var) (C:cname) (v:Value) (body:exp) :=
     (EBlk (x::nil) ((Dec (DTCl C None) x (proj1_sig v))::nil)  body).


(** Substitution [subst x C e e'] returns e' in which free occurrences of x are substituted
   with e, where [C] is the class of [e]. We assume that [e] is a value associated with an 
   affine variable, so it is a closed value (no free variable can be captured). *)

Fixpoint subst (x:var) C (e:Value) (e':exp) {struct e'} : exp :=
  match e' with
  | (EVar y)         => if (y==x) then (proj1_sig e) else e'
  | (ENew C xs)      => if (is_in x xs) then  (mk_block_with_def x C e (ENew C xs))
                       else e'
  | (EFld y f)      => if (y==x) then (mk_block_with_def x C e (EFld y f))
                       else e'
  | (EUpd y1 f y2)   => if (is_in x (y1::y2::nil)) then (mk_block_with_def x C e (EUpd y1 f y2))
                        
                        else e'
  | (EBlk ann ds eb) => 
       EBlk ann ((fix subst_ds (ds: list dec) {struct ds}: (list dec) :=
                    match ds with
                    | nil                 => nil
                    | (Dec dt z ez)::tlds => (Dec dt z  (subst C x e ez) )::(subst_ds tlds)
                    end
                  ) ds)
                (subst C x e  eb)
  | _ => e'
end.


(** Evaluation contexts *)



Inductive ev_ctx : Type :=
   | Hole    : ev_ctx
   | ECBlDec   : blAnnotation -> (list dec) -> ev_dec_ctx -> (list dec) -> exp ->  ev_ctx
   | ECBlBody  : blAnnotation -> (list dec) -> ev_ctx -> ev_ctx

with ev_dec_ctx : Type :=
   ECDec : decTy -> var -> ev_ctx -> ev_dec_ctx.


(** Evaluation contexts to be used in the evalution: specify the evaluation order *)

Inductive  ok_ev_ctx : ev_ctx ->Prop :=
   | ok_hole   : ok_ev_ctx Hole
   | ok_Dec    : forall ann dvs ds eb eC dty x,
                             (Forall ev_dec dvs)->
                             (Forall (fun d => ~ ev_dec d) ds)->
                             (ok_ev_ctx eC)->
                             ok_ev_ctx (ECBlDec ann dvs (ECDec dty x eC) ds  eb)
   | ok_Body   : forall ann dvs eC,
                             (Forall ev_dec dvs) ->
                             (ok_ev_ctx eC) ->  
                             ok_ev_ctx (ECBlBody ann dvs eC).
   

Fixpoint vars2exps vs:list exp :=
match  vs with
| nil => nil
| x::tl =>(EVar x)::(vars2exps tl)
end. 


(** Returns the expression evCtx[e] *)

Fixpoint apply_ev_ctx eC e  {struct eC}: exp := 
match eC with
| Hole  => e
| (ECBlDec ann dvs (ECDec dt x ebC) ds eb) =>  
         (EBlk ann (dvs++((Dec dt x (apply_ev_ctx ebC e))::nil)++ds) eb)
| (ECBlBody ann dvs eCB) =>  (EBlk ann dvs (apply_ev_ctx eCB e))
end.


(** Returns true if x is declared in the evaluated declarations of eC false otherwise *)
Fixpoint is_dec_ctx eC x  {struct eC}: bool := 
match eC with
| Hole  => false
| (ECBlDec ann dvs (ECDec dt y ebC) ds eb) =>  
    if (dec_in_ds x dvs) then
      true
    else 
      (is_dec_ctx ebC x)
| (ECBlBody ann dvs eCx) =>  
    if (dec_in_ds x dvs) then
      true
    else 
      (is_dec_ctx eCx x)
end.


(** Returns the innermost declaration of x if x is declared in the evaluated declarations of eC  *)
Fixpoint dec_ctx eC x  {struct eC}: option dec := 
match eC with
| Hole  => None
| (ECBlDec ann dvs (ECDec dt y ebC) ds eb) =>  
    if ((dec_in_ds x dvs) && (negb(is_dec_ctx ebC x))) then
      (get_dec_in_ds x dvs)
    else 
      (dec_ctx ebC x)
| (ECBlBody ann dvs eCx) =>  
    if ((dec_in_ds x dvs) && (negb(is_dec_ctx eCx x))) then
      (get_dec_in_ds x dvs)
    else 
      (dec_ctx eCx x)
end.



Definition dec_ctx_P eC x d: Prop := dec_ctx eC x=Some d.


(** Given an evaluation context, eC, and a variable, x, declared inside one of its blocks
   returns a pair of evaluation contexts (eCx,eCr) such that eC=eCx[eCr] and eCx={dvs []} 
   or eCx={dvs T y=[] ds2 eb} and x is declared in dvs **)


Fixpoint ev_ctx_dec_x eC x  {struct eC}: (ev_ctx * ev_ctx) := 
match eC with
| Hole  => (Hole,Hole)
| (ECBlDec ann dvs (ECDec dt y eCx) ds eb) =>   
    if ((dec_in_ds x dvs) && (negb(is_dec_ctx eCx x))) then
      ((ECBlDec ann dvs (ECDec dt y Hole) ds eb),eCx)
    else 
      let (eC1,eC2):=(ev_ctx_dec_x  eCx x) in   
        ((ECBlDec ann dvs (ECDec dt y eC1) ds eb),eC2)
| (ECBlBody ann dvs eCx) =>  
    if ((dec_in_ds x dvs) && (negb(is_dec_ctx eCx x))) then
      ((ECBlBody ann dvs Hole),eCx)
    else 
      let (eC1,eC2):=(ev_ctx_dec_x  eCx x) in   
        ((ECBlBody ann dvs eC1),eC2)
end.

(**  Redexes:  x.f | x.f=y | {X dvs C^a x=v ds e} | {X dvs C x=(y | tr | fls | n) ds e}
             | 

*)
(** 
  Decomposition: given [e] not a value returns eC and e' such that e=eC[e']
  and e' is either [x.f] or  [x.f=y] or [{X dvs C^Affine x=v ds e}]
  or [{X dvs C^_ x=y ds e}] or ..............
*)


(*

  
Inductive eval : ev_ctx -> exp -> exp -> Prop :=
| eval_fld : forall  eC x t C es f fs fes e, 
    dec_ctx_P eC x (Dec t x (ENew C es)) ->
    fields C fs ->
    env_zip fs es fes ->
    binds f e fes ->
    eval eC (EFld x f) 
|eval_udp:

    eval eC (EUpd (EVar x) f (EVar y)) eC' e (EVar y).

*)






