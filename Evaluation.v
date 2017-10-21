(***************************************************************************
 * Tracing sharing in an imperative pure calculus: evaluation
 *  
 ***************************************************************************)


(** This library contains the definition of the operational semantics of the 
    language.
    We define: values, capture free substitution (renaming of bound variables),
    evaluation contexts with the operations of renaming (when we want a capture
    free  substitution in the hole of the context) and update.
    Finally we define the evaluation. *)
    
    
Require Import List.

Require Import Metatheory.
Require Import TypedLanguage.
Require Import Coq.Bool.Bool.

(** Values and evaluated declarations *)

Inductive prim_value : exp -> Prop :=
| val_num : forall n, prim_value (ENum n)
| val_tr  : prim_value ETrue
| val_fls : prim_value EFalse.


Inductive value : exp -> Prop :=
   | val_x   : forall x, value (EVar x)
   | val_prim : forall val, prim_value val -> value val
   | val_new : forall C vs,
               (Forall value vs) ->
               (value (ENew C vs))
   | val_blk : forall ann dvs v,
               (ev_decs dvs) ->
               (value v) ->
               (value (EBlk ann dvs  v))

with
ev_decs : (list dec) -> Prop :=
   |dvs_nil  : (ev_decs nil)
   |dvs_cons : forall dvs C x vs,
               (ev_decs dvs) ->
               (Forall value vs) ->
               (ev_decs   ((Dec (DTCl C None) x (ENew C vs))::dvs)).


(** Substitution of one variable with another: renaming, alpha renaming, and alpha congruence *)

Definition rename := (list (var * var)).


(** Renaming of expressions: substitution of variables with variables    *)

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
  | (ENew C es)     => (ENew C (List.map (rename_exp rn) es))
  | (EFld e1 f)     => (EFld (rename_exp rn e1) f) 
  | (EUpd e1 f e2)  => (EUpd (rename_exp rn e1) f (rename_exp rn e2)) 
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

(** Alpha-renaming of declarations and blocks  *)


Fixpoint alpha_rename_ds (x:var) (y:var) (ds:list dec) : list dec :=
  match ds with
  | nil                 => nil
  | (Dec dt z ez)::tlds => 
        if (z==x)  then
          (Dec dt y (rename_exp ((x,y)::nil) ez))::(alpha_rename_ds x y tlds)
        else  (Dec dt z (rename_exp ((x,y)::nil) ez))::(alpha_rename_ds x y tlds)
end.

Fixpoint alpha_renames_ds (rn:rename) (ds:list dec): list dec :=
  match rn with
  | nil        => ds
  | (x,y)::tlr => alpha_renames_ds tlr (alpha_rename_ds x y ds)
end.

Fixpoint alpha_renames_block (rn:rename) (bl:exp): exp :=
  match bl with
  | (EBlk ann ds  e) => 
       (EBlk (rename_ann rn ann) 
             (alpha_renames_ds rn ds)
             (rename_exp rn e)
       )      
  | _ => bl
end.
  
(** Substitution  *)

(** [make_ok_for_subst x e e'], returns [e'] in which blocks declaring variables
   free in [e] are alpha-renamed to fresh variables. Blocks in which x is declared
   remain unchanged. *)


Fixpoint make_ok_for_subst (x:var) (e:exp) (e':exp) {struct e'}: exp :=
  match e' with
  | (EVar y)         => (EVar y)
  | (ENew C es)      => (ENew C (List.map (make_ok_for_subst x e) es))
  | (EFld e1 f)      => (EFld (make_ok_for_subst x e e1) f)
  | (EUpd e1 f e2)   => (EUpd (make_ok_for_subst x e e1) f (make_ok_for_subst x e e2)) 
  | (EBlk ann ds eb) =>
      if (dec_in_ds x ds) then EBlk ann ds eb
      else 
        let xs := (set_inter eq_atom_dec (free_var e) (dec_vars ds)) in
          let rn := zip xs (fresh_vars (length  xs) 
                                       (set_union eq_atom_dec (free_var e) 
                                           (blockVars  (EBlk ann ds eb) ) ) ) in
            let eb':=(make_ok_for_subst x e eb) in
              (alpha_renames_block rn (EBlk ann ds eb'))
  | _                => e'
end.



(** Substitution [subst x e e'] returns e' in which free occurrences of x are substituted
   with e. No check is done for blocks that may declare variables free in e. *)

Fixpoint subst_ok (x:var) (e:exp) (e':exp) {struct e'} : exp :=
  match e' with
  | (EVar y)         => if (y==x) then e else e'
  | (ENew C es)      => ENew C (List.map (subst_ok x e) es)
  | (EFld e1 f)      => EFld (subst_ok x e e1) f
  | (EUpd e1 f e2)   => EUpd (subst_ok x e e1) f (subst_ok x e e2)
  | (EBlk ann ds eb) => 
      if (dec_in_ds x ds) then EBlk ann ds eb
      else
         EBlk ann ((fix subst_ds (ds: list dec) {struct ds}: (list dec) :=
                    match ds with
                    | nil                 => nil
                    | (Dec dt z ez)::tlds => (Dec dt z  (subst_ok x e ez) )::(subst_ds tlds)
                    end
                  ) ds)
                (subst_ok x e  eb)
  | _ => e'
end.

(* Substitution [subst x e e'] returns e' in which free occurrences of x are substituted 
   with e. Inner blocks declaring variables free in e are alpha-renamed to fresh variables. *)

Definition subst (x:var) (e:exp) (e':exp): exp :=
  subst_ok x e (make_ok_for_subst x e e').

Fixpoint subst_ds (x:var) (e:exp) (ds:list dec): list dec  :=
match ds with
| nil => nil
| (Dec dt z ez)::tlds => (Dec dt z (subst x e ez) )::(subst_ds x e tlds)
end.
  
(* I would have liked to write the following, in which alpha-renamaing is done along with the
 substitution, but Coq complains because the inner call [(subst x e ez)] is on the wrong 
 inductive parameters *)

(*
Fixpoint subst (x:var) (e:exp) (e':exp) {struct e'}: exp :=
match e' with
|(EVar y) => if (y==x) then e else e'
|(ENew C es) => (ENew C (List.map (subst x e) es))
|(EFld e1 f) => (EFld (subst x e e1) f)
|(EUpd e1 f e2) => (EUpd (subst x e e1) f (subst x e e2)) 
|(EBlk ann ds eb) => 
  ( if ((dec_in_ds x ds)  ) then (EBlk ann ds eb)
    else ( let xs:=(set_inter eq_atom_dec (free_var e) (dec_vars ds)) 
           in  let rn:=(zip xs (fresh_vars (length  xs) (set_union eq_atom_dec (free_var e) (dec_vars ds))))
           in (EBlk 
                (rename_ann rn ann)
                ( (fix subst_ds (ds: list dec) {struct ds}: (list dec) :=
                        match ds with
                        | nil => nil
                        | (Dec dt z ez)::tlds => (Dec dt z  (subst x e ez) )::(subst_ds tlds)
                                         
                    end
                   )  
                   (alpha_renames_ds rn ds)  
                ) 
               (subst x e  (* (rename_exp rn eb) *) eb)
               )   
         )
  )                                           
| _ => e'
end. 
*)

(* Normalizing expressions using "congruence" 

*)



(** Evaluation contexts *)

Inductive ev_ctx : Type :=
   | Hole   : ev_ctx
   | ECDec  : blAnnotation -> list ev_dec -> decTy -> var -> ev_ctx -> list dec -> exp ->  ev_ctx
   | ECBody : blAnnotation -> list ev_dec -> ev_ctx -> ev_ctx

with ev_dec : Type :=
   EvDec : cname -> var -> list var -> ev_dec.


(** Conversion of variables to expressions  *)

Fixpoint vars2exps vs:list exp :=
match  vs with
| nil => nil
| x::tl =>(EVar x)::(vars2exps tl)
end. 

(** Conversion of evaluated declarations to declarations and test for evaluated declarations *)


Fixpoint evDecs2decs (eD:list ev_dec):list dec :=
match  eD with
| nil => nil
| (EvDec C x vs)::tl =>(Dec (DTCl C None) x (ENew C (vars2exps vs)))::(evDecs2decs tl)
end.

Inductive is_var: exp -> Prop := 
   | var_x : forall x, is_var (EVar x).


   
Definition alpha_renames_ev_dec (rn:rename) (dv:ev_dec): ev_dec :=
match dv with
| (EvDec C x xs) => (EvDec C (rename_var rn x) (rename_vars rn xs) )
end.

Fixpoint alpha_renames_dvs (rn:rename) (dvs:list ev_dec): list ev_dec :=
  match dvs with
  | nil  => nil
  | dv::tlDv => (alpha_renames_ev_dec rn dv)::(alpha_renames_dvs rn tlDv)
end.

(** [comp_ev_ctxs eC eC'] returns [eC[eC']] *)

Fixpoint comp_ev_ctxs eC eC'  {struct eC}: ev_ctx := 
match eC with
| Hole  => eC'
| (ECDec ann dvs dTy z eCin ds eb) =>  (ECDec ann dvs dTy z (comp_ev_ctxs eCin eC') ds eb)
| (ECBody ann dvs eCin) =>  (ECBody ann dvs (comp_ev_ctxs eCin eC'))
end.

(** [free_vars_eC eC] returns the set of free variables in eC. *)

Fixpoint free_var_eC (eC: ev_ctx): (set var) :=
   let ed := eq_atom_dec in   
     match eC with
     | Hole        =>  (@empty_set var)
     |(ECDec ann dvs dTy z eC' ds eb) => 
            (set_diff ed 
               ( set_union ed (free_var_ds ((evDecs2decs dvs)++ds) )
                  ( set_union ed (free_var_eC eC') (free_var eb) )
               )    
             (z::((dec_vars ds)++(dec_vars (evDecs2decs dvs))))
            )      
     |(ECBody ann dvs eC')  => 
            (set_diff ed               
                  ( set_union ed (free_var_eC eC') (free_var_ds (evDecs2decs dvs)) ) 
             (dec_vars (evDecs2decs dvs))
            ) 
end.

(** [ev_ctx_no_capt eC xs] returns eC in which variables in xs which are bound in eC
    are renamed away from xs U vars of the block in which they are declared. *)

Fixpoint ev_ctx_no_capt eC xs  {struct eC}: ev_ctx := 
match eC with
| Hole  => Hole
| (ECDec ann dvs dTy z eC' ds eb) => 
     let eCR:=(ev_ctx_no_capt eC' xs) in
     let ds':= (evDecs2decs dvs)++ds in
     let ys:= (set_inter eq_atom_dec xs (z::(dec_vars ds') ) ) in
     let rn:=(zip ys (fresh_vars (length  ys) (set_union eq_atom_dec (free_var_eC eCR) 
                                                             (z::(vars ds'))  ) ) ) in
     (ECDec (rename_ann rn ann) 
            (alpha_renames_dvs rn dvs)
            dTy (rename_var rn z) eCR
            (alpha_renames_ds rn ds)
             (rename_exp rn eb)
      )        
| (ECBody ann dvs eC') => 
     let eCR:=(ev_ctx_no_capt eC' xs) in
     let ys:= (set_inter eq_atom_dec xs (dec_vars (evDecs2decs dvs))) in
     let rn:=(zip ys (fresh_vars (length  ys) (set_union eq_atom_dec (free_var_eC eCR) 
                                                              (vars (evDecs2decs dvs))  ) ) ) in
     (ECBody (rename_ann rn ann) 
             (alpha_renames_dvs rn dvs)
             eCR)        
        
end.


(** [is_dec_ctx eC x] Returns true if x is declared in the evaluated declarations of eC false otherwise *)

Fixpoint is_dec_ctx eC x  {struct eC}: bool := 
match eC with
| Hole  => false
| (ECDec ann dvs dTy v eCx ds eb) =>  
    if (dec_in_ds x (evDecs2decs dvs)) then
      true
    else 
      (is_dec_ctx eCx x)
| (ECBody ann dvs eCx) =>  
    if (dec_in_ds x (evDecs2decs dvs)) then
      true
    else 
      (is_dec_ctx eCx x)
end.

Definition is_dec_ctx_P eC x :Prop := is_dec_ctx eC x=true.

(** [dec_ctx eC x] returns the innermost declaration of x if x is declared in the evaluated declarations of eC  *)

Fixpoint dec_ctx eC x  {struct eC}: option dec := 
match eC with
| Hole  => None
| (ECDec ann dvs dTy v eCx ds eb) =>  
    if ((dec_in_ds x (evDecs2decs dvs)) && (negb(is_dec_ctx eCx x))) then
      (get_dec_in_ds x (evDecs2decs dvs))
    else 
      (dec_ctx eCx x)
| (ECBody ann dvs eCx) =>  
    if ((dec_in_ds x (evDecs2decs dvs)) && (negb(is_dec_ctx eCx x))) then
      (get_dec_in_ds x (evDecs2decs dvs))
    else 
      (dec_ctx eCx x)
end.

Definition dec_ctx_P eC x d: Prop := dec_ctx eC x=Some d.


(** Given an evaluation context eC and a variable x declared inside eC
   returns a pair of evaluation contexts (eCx,eCr) such that eC=eCx[eCr] and eCx={dvs []} 
   or eCx={dvs T y=[] ds2 eb} and x is declared in dvs *)


Fixpoint ev_ctx_dec_x eC x  {struct eC}: (ev_ctx * ev_ctx) := 
match eC with
| Hole  => (Hole,Hole)
| (ECDec ann dvs dTy v eCx ds eb) =>  
    if ((dec_in_ds x (evDecs2decs dvs)) && (negb(is_dec_ctx eCx x))) then
      ((ECDec ann dvs dTy v Hole ds eb),eCx)
    else 
      let (eC1,eC2):=(ev_ctx_dec_x  eCx x) in   
        ((ECDec ann dvs dTy v eC1 ds eb),eC2)
| (ECBody ann dvs eCx) =>  
    if ((dec_in_ds x (evDecs2decs dvs)) && (negb(is_dec_ctx eCx x))) then
      ((ECBody ann dvs Hole),eCx)
    else 
      let (eC1,eC2):=(ev_ctx_dec_x  eCx x) in   
        ((ECBody ann dvs eC1),eC2)
end.

Definition ev_ctx_dec_x_P eC x eCx eCin: Prop := ev_ctx_dec_x eC x = (eCx,eCin).



(** [split_dvs x dvs] partitions the evaluated declarations in dvs in the ones before and
    after the declaration of x. Adapted by the same function for [ds].  [split_dvs_aux]
    is used to give a tail recursive definition. *)

Fixpoint split_dvs_aux (x:var) dvs1 dvs2:=
   match dvs2 with 
   | nil => (dvs1,dvs2)
   | (EvDec C y ys)::tlDvs => 
        if (x==y) then (dvs1,(EvDec C y ys)::dvs2) 
        else (split_dvs_aux x (dvs1 ++ ((EvDec C y ys)::nil)) tlDvs)
end.

Definition split_dvs x dvs:=(split_dvs_aux x nil dvs).

(** [dec_in_dvs x dvs] returns true if [x] is declared in [dvs]. Adapted by the same function for [ds].  *)

Definition dec_in_dvs x dvs : bool:=
   let (dvs1,dvs2):=(split_dvs x dvs) in
      match dvs2 with
      | d::tl => true
      | nil => false  
      end.

(** [get_dec_in_dvs x dvs] returns the evaluated declarations of [x] in in [dvs] (if any).
     Adapted by the same function for [ds].  *)

Definition get_dec_in_dvs x dvs : option ev_dec:=
   let (dvs1,dvs2):=(split_dvs x dvs) in
      match dvs2 with
      | d::tl => Some d
      | nil => None  
      end.

(** [upd_dvs dvs x f fs y] returns the evaluated declarations [dvs] in which the declaration
    of [x] (if any) has the field [f] updated to [y].  *)

Fixpoint upd_field  (fs:list fname) f zs y: list var:=
      match fs,zs with
      | nil,_ => nil
      | _,nil => nil
      | fC::fTl,zC::zTl => 
          if (fC==f) then y::zTl
          else zC::(upd_field fTl f zTl y)          
      end.
            
Definition upd_dvs dvs x f (fs:list fname) y: list ev_dec:=
   let (dvs1,dvs2):=(split_dvs x dvs) in
      match dvs2 with
      | nil => dvs
      | (EvDec C z zs)::tl => dvs1++((EvDec C z (upd_field fs f zs y))::tl)
      end.      
      

(** [upd_ev_ctx eC x f y] returns an evaluation context in which the field [f] of the 
    innermost declaration of [x] (in an evaluted declaration) if any is updated to [y] *)
   
Fixpoint upd_ev_ctx eC x (fs:list fname) f y: ev_ctx  := 
match eC with
| Hole  => Hole
| (ECDec ann dvs dTy v eCx ds eb) =>  
    if ((dec_in_dvs x dvs) && (negb(is_dec_ctx eCx x))) then
      (ECDec ann (upd_dvs dvs x f fs y) dTy v eCx ds eb)
    else 
      let eCx':=(upd_ev_ctx eCx x fs f y) in   
        (ECDec ann dvs dTy v eCx' ds eb)
| (ECBody ann dvs eCx) =>  
    if ((dec_in_ds x (evDecs2decs dvs)) && (negb(is_dec_ctx eCx x))) then
       (ECBody ann (upd_dvs dvs x f fs y) eCx)
    else 
      let eCx':=(upd_ev_ctx eCx x fs f y) in   
        (ECBody ann dvs eCx')
end.

(** Evaluation *)

Inductive eval : ev_ctx -> exp -> ev_ctx -> exp -> Prop :=
| eval_fld : forall  eC x t C es f fs fes xf, 
    dec_ctx_P eC x (Dec t x (ENew C es)) ->
    fields C fs ->
    env_zip fs es fes ->
    binds f (EVar xf) fes ->
    eval eC (EFld (EVar x) f) (ev_ctx_no_capt eC (xf::nil)) (EVar xf)
| eval_upd :forall  eC x f y t C es fs fes xf eCx eCin, 
    dec_ctx_P eC x (Dec t x (ENew C es)) ->
    fields C fs ->
    env_zip fs es fes ->
    binds f (EVar xf) fes ->
    ev_ctx_dec_x_P eC x eCx eCin ->
    is_dec_ctx_P eCx y->     
    eval eC (EUpd (EVar x) f (EVar y)) (comp_ev_ctxs (upd_ev_ctx eCx x (dom fs) f y) eCin) (EVar y) 
| eval_alias_elim:forall eC a dvs t x y ds eb,
    (ev_decs dvs) ->
    eval eC (EBlk a (dvs++((Dec t x (EVar y))::ds)) eb) 
         eC (EBlk (rename_ann ((x,y)::nil) a) (dvs++((rename_ds ((x,y)::nil) ds) ) ) (rename_exp ((x,y)::nil) eb) )
| eval_capsule_elim:forall eC a dvs C x val ds eb,
    (ev_decs dvs) ->
    (value val) ->
    eval eC (EBlk a (dvs++((Dec (DTCl C (Some Affine)) x val)::ds)) eb) 
         eC (EBlk a (dvs++((subst_ds x val ds) ) ) (subst x val eb) )
| eval_const_elim:forall eC a dvs t x ds eb val,
    (ev_decs dvs) ->
    (prim_value val) ->
    eval eC (EBlk a (dvs++((Dec t x val)::ds)) eb) 
         eC (EBlk a (dvs++((subst_ds x val ds) ) ) (subst x val eb) )         
.









