(***************************************************************************
 * Tracing sharing in an imperative pure calculus: evaluation
 *  
 ***************************************************************************)

Require Import List.

Require Import TypedLanguage.
Require Import Metatheory.


(* Values *)

(* [value exp] holds if [exp] is a value, [ev_dec dvs] holds of the declarations 
    in [dvs] are all evaluated 
*)
   
Inductive value : exp -> Prop :=
| val_x : forall x, value (EVar x)
| val_num : forall n, value (ENum n)
| val_tr : value ETrue
| val_fls : value EFalse
| val_new : 
     forall C vs,
        (Forall value vs) ->
        (value (ENew C vs) )
| val_blk: 
     forall ann dvs v,
        (ev_decs dvs) ->
        (value v) ->
        (value (EBlk ann dvs  v))
        
with
ev_decs: (list dec) -> Prop :=
|dvs_nil : (ev_decs nil)
|dvs_cons : forall dvs C x vs,
    (ev_decs dvs) ->
    (Forall value vs) ->
    (ev_decs   ((Dec (DTCl C None) x (ENew C vs))::dvs)).
    
    
(* Canonical Values *)


Inductive is_var: exp -> Prop := 
| var_x : forall x, is_var (EVar x).




Inductive connected: (list dec) -> (list var) -> Prop:=
| is_def : forall dvs xs,
   (incl (dec_vars dvs) xs) ->  (connected dvs xs)
| is_free_def : forall dvs dvs1 dvs2 xs,
   ((dvs = dvs1++dvs2) /\ (connected dvs1 xs) /\ (connected dvs2 (free_var_es (dec_es dvs1))))
   -> (connected dvs xs).

(* [c_value exp] holds if [exp] is a canonical value, [c_ev_dec dvs] holds of the 
   declarations in [dvs] are all canonical evaluated declarations 
*)

Inductive c_value: exp -> Prop :=
| c_val_x : forall x, c_value (EVar x)
| c_val_num : forall n, c_value (ENum n)
| c_val_tr : c_value ETrue
| c_val_fls : c_value EFalse
| c_val_blk: 
     forall x dvs ann,
        (c_ev_decs dvs) ->
        (connected dvs (x::nil)) ->
        (c_value (EBlk ann dvs  (EVar x)))

with
c_ev_decs: (list dec) -> Prop :=
|c_dvs_nil : (c_ev_decs nil)
|c_dvs_cons : forall dvs C x vs,
    (c_ev_decs dvs) ->
    (Forall is_var vs) ->
    (c_ev_decs   ((Dec (DTCl C None) x (ENew C vs))::dvs)).
    
 

Lemma var_is_value (e : exp) : is_var e -> value e.
Proof.
intro.
destruct H.
exact (val_x x).
Qed.


(* 
  All canonical evaluated declarations are evaluated declarations
*)

Lemma c_ev_dec_is_evDec: forall dvs,  (c_ev_decs dvs) ->(ev_decs dvs).
Proof.
intros.
induction H.
  - apply dvs_nil.
  - pose (Forall_impl value var_is_value H0).
    apply dvs_cons.
exact IHc_ev_decs.
exact f.

Qed.

(* 
  All canonical values are values
*)
Lemma c_val_is_val: forall v,  (c_value v) ->(value v).
Proof.
intro H.
intro V.
induction V.
  - apply val_x.
  - apply val_num.
  - apply val_tr.
  - apply val_fls.
  - apply val_blk.
      pose (dvs_proof:=c_ev_dec_is_evDec dvs H).
      exact dvs_proof.
      
      exact (val_x x).
Qed.





(* Substitution of one variable with another: alpha rename  and alpha congruence 

*)

 
Definition rename := (list (var * var)).

Fixpoint rename_var (rn:rename) (x:var)  : var :=
match rn with
| nil => x 
| (z,y)::tlr =>( if (z==x) then y else (rename_var tlr x) )
end.

Fixpoint rename_vars (rn:rename) (xs:list var)  : list var :=
match xs with
|nil => nil
|x::tlx => (rename_var rn x)::(rename_vars rn tlx)
end.                    


Definition rename_ann (rn:rename) (ann:blAnnotation): blAnnotation := (rename_vars rn ann).                    

Print EBlk.

Fixpoint rename_exp (rn:rename) (e:exp) {struct e}: exp :=
match e with
|(EVar x) => (EVar (rename_var rn x)) 
|(ENew C es) => (ENew C (List.map (rename_exp rn) es))
|(EFld e1 f) => (EFld (rename_exp rn e1) f) 
|(EUpd e1 f e2) => (EUpd (rename_exp rn e1) f (rename_exp rn e2)) 
|(EBlk a ds e) => (EBlk (rename_ann rn  a) 
                          ((fix rename_ds (ds:list dec) : (list dec):=
                           match ds with
                           |nil => nil
                           |(Dec dt z ez)::tl => (Dec dt z (rename_exp rn ez))::(rename_ds tl)
                           end
                          )   ds)
                          (rename_exp rn e)
                     )
|ek => ek
end.


Fixpoint rename_ds (rn:rename) (ds:list dec) : (list dec):=
match ds with
|nil => nil
|(Dec dt z e)::tl => (Dec dt z (rename_exp rn e))::(rename_ds rn tl)
end.


Fixpoint alpha_rename_ds (x:var) (y:var) (ds:list dec): list dec :=
match ds with
|nil => nil
|(Dec dt z ez)::tlds => 
       (if (z==x)  then
          (Dec dt y (rename_exp ((x,y)::nil) ez))::(alpha_rename_ds x y tlds)
        else  (Dec dt z ez)::(alpha_rename_ds x y tlds)
       )      
end.
  

Inductive alpha_cong: exp -> exp ->Prop:=
|cong_fld : forall e1 e2 f,
    alpha_cong e1 e2 ->
    alpha_cong (EFld e1 f) (EFld e2 f)
|cong_upd : forall e1 e2 e3 e4 f,
    (alpha_cong e1 e3) ->
    (alpha_cong e2 e4) ->
    alpha_cong (EUpd e1 f e2) (EUpd e3 f e4)    
|cong_new : forall es es' C,
    alpha_cong_es es es' ->
    alpha_cong (ENew C es) (ENew C es')
|cong_blk : forall ann ds e dt x ds1 ds2 ds3 ex y,
    (split_dec x ds)=(ds1,ds2) ->
    ds2=(Dec dt x ex)::ds3 ->
    ( not (In y (dec_vars ds)) )->
    alpha_cong (EBlk ann ds  e) 
               (EBlk (rename_ann ((x,y)::nil) ann) 
                     (alpha_rename_ds x y ds)
                     (rename_exp ((x,y)::nil) e) 
               ) 
|cong_id: forall e:exp,  alpha_cong e e
|cong_trans : forall e1 e2 e3,
    (alpha_cong e1 e2) ->
    (alpha_cong e2 e3) ->
    (alpha_cong e1 e3)     
|cong_sym: forall e1 e2,  
    (alpha_cong e1 e2) ->
    (alpha_cong e2 e1)     

with alpha_cong_es: (list exp) -> (list exp) ->Prop:=
|cong_nil: alpha_cong_es nil nil
|cong_cons : forall e e' es es', 
   alpha_cong e e' -> 
   alpha_cong_es es es' ->
   alpha_cong_es (e::es) (e'::es').


(* [fresh_vars n ys], returns a list of n different fresh variables such that none
  of them is in [ys] *) 

Definition fresh_var (xs:list var) : var :=(proj1_sig (atom_fresh_for_list xs)). 


Fixpoint fresh_vars (n:nat)  (ys:list var) : list var :=
match n with
   |0 => nil
   |(S m) => ( let z:=(proj1_sig (atom_fresh_for_list ys)) in
                   z::(fresh_vars m (z::ys))
             )  
end. 


Fixpoint zip (xs:list var)  (ys:list var) : list (var * var):=
match xs,ys with
   |nil,_ => nil
   |_,nil => nil
   |x::tlx,y::tly => (x,y)::(zip tlx tly)
end.


Fixpoint alpha_renames_ds (rn:rename) (ds:list dec): list dec :=
match rn with
|nil => ds
|(x,y)::tlr => alpha_renames_ds tlr (alpha_rename_ds x y ds)
end.

(* [make_ok_for_subst x e e'], returns e' in which blocks declaring variables free in e are 
   alpha-renamed to fresh variables. *)

Fixpoint make_ok_for_subst (x:var) (e:exp) (e':exp) {struct e'}: exp :=
match e' with
|(EVar y) => (EVar y)
|(ENew C es) => (ENew C (List.map (make_ok_for_subst x e) es))
|(EFld e1 f) => (EFld (make_ok_for_subst x e e1) f)
|(EUpd e1 f e2) => (EUpd (make_ok_for_subst x e e1) f (make_ok_for_subst x e e2)) 
|(EBlk ann ds eb) => 
  ( if ((dec_in_ds x ds)  ) then (EBlk ann ds eb)
    else ( let xs:=(set_inter eq_atom_dec (free_var e) (dec_vars ds)) 
           in  let rn:=(zip xs (fresh_vars (length  xs) (set_union eq_atom_dec (free_var e) (dec_vars ds))))
           in (EBlk 
                (rename_ann rn ann)
                (alpha_renames_ds rn ds)
                (make_ok_for_subst x e  eb)
               )   
         )
  )                                           
| _ => e'
end.

(* Substitution [subst x e e'] returns e'in which free occurrences of x are substituted with e.
   No check is done for blocks that may declare variables free in e. *)
   
Fixpoint subst_ok (x:var) (e:exp) (e':exp) {struct e'}: exp :=
match e' with
|(EVar y) => if (y==x) then e else e'
|(ENew C es) => (ENew C (List.map (subst_ok x e) es))
|(EFld e1 f) => (EFld (subst_ok x e e1) f)
|(EUpd e1 f e2) => (EUpd (subst_ok x e e1) f (subst_ok x e e2)) 
|(EBlk ann ds eb) =>
              (EBlk 
                ann
                ((fix subst_ds (ds: list dec) {struct ds}: (list dec) :=
                        match ds with
                        | nil => nil
                        | (Dec dt z ez)::tlds => (Dec dt z  (subst_ok x e ez) )::(subst_ds tlds)
                                         
                    end
                   )  
                   ds
                )
                (subst_ok x e  eb)
               )                                           
| _ => e'
end.

(* Substitution [subst x e e'] returns e'in which free occurrences of x are substituted with e.
   Inner blocks declaring variables free in e are alpha-renamed to fresh variables. *)

Definition subst (x:var) (e:exp) (e':exp): exp :=(subst_ok x e (make_ok_for_subst x e e')).


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



