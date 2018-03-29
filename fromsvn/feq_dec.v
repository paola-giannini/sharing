Inductive fin : nat -> Set :=
| F1 : forall {n : nat}, fin (S n)
| FS : forall {n : nat}, fin n -> fin (S n).

Definition C {m : nat} (x : fin (S m)) :=
  { x' | x = FS x' } + { x = F1 }.

Definition case {m : nat} (x : fin (S m)) : C x :=
match x in fin (S n) return { x' | x = FS x' } + { x = F1 } with
  | F1    => inright eq_refl
  | FS x' => inleft (exist _ x' eq_refl)
end.

Definition finpred {m : nat} (x : fin m) : option (fin (pred m)) :=
match x with
  | F1    => None
  | FS x' => Some x'
end.

Definition P {m : nat} (x y : fin m) := {x = y} + {x <> y}.

Fixpoint feq_dec {m : nat} (x y : fin m) : P x y.
refine (
match m return forall (x y : fin m), P x y with
  | O    => _
  | S m' => fun x y =>
  match (case x, case y) with
    | (inright eqx            , inright eqy)             => left _
    | (inleft (exist _ x' eqx), inright eqy)             => right _
    | (inright eqx            , inleft (exist _ y' eqy)) => right _
    | (inleft (exist _ x' eqx), inleft (exist _ y' eqy)) =>
    match feq_dec _ x' y' with
      | left eqx'y'   => left _
      | right neqx'y' => right _
    end
  end
end x y);simpl in *; subst.
- inversion 0.
- reflexivity.
- intro Heq; apply neqx'y'.
  assert (Heq' : Some x' = Some y') by exact (f_equal finpred Heq).
  inversion Heq'; reflexivity.
- inversion 1.
- inversion 1.
- reflexivity.
Defined.

Compute (@feq_dec 5 (FS F1) (FS F1)).

(*  this is from https://stackoverflow.com/questions/45264094/dependent-pattern-matching-on-two-values-with-the-same-type
    (and the code from https://gist.github.com/gallais/7b12caa45199431a3a1209142f6408db )

The function defined this way works as expected:

Compute (@feq_dec 5 (FS F1) (FS F1)).
(* 
 = left eq_refl
 : P (FS F1) (FS F1)
*)

This code relies on 3 tricks:
1. Start by inspecting the bound m.

Indeed if you don't know anything about the bound m, you'll learn two 
different facts from the match on x and y respectively and you'll need 
to reconcile these facts (i.e. show that the two predecessor for m you're 
given are in fact equal). If, on the other hand, you know that m has the 
shape S m' then you can...

2. Use a case function inverting the term based on the bound's shape

If you know that the bound has a shape S m' then you know for each one of 
your fins that you are in one of two cases: either the fin is F1 or it is 
FS x' for some x'. case makes this formal:

   (see code above)

Coq will be smart enough to detect that the values we are returning from
case are direct subterms of the arguments it takes. So performing recursive
calls when both x and y have the shape FS _ won't be a problem!

3. Use congruence with an ad-hoc function to peel off constructors

In the branch where we have performed a recursive call but got a negative answer
in return, we need to prove FS x' <> FS y' knowing that x' <> y'. Which means 
that we need to turn Heq : FS x' = FS y' into x' = y'.

Because FS has a complicated return type, simply performing inversion on Heq won't 
yield a usable result (we get an equality between dependent pairs of a nat p and a 
fin p). This is were finpred comes into play: it's a total function which, when 
faced with FS _ simply peels off the FS constructor.

   (see code above)

Combined with f_equal and Heq we get a proof that Some x' = Some y' on which we can 
use inversion and get the equality we wanted.
