
(* Notations for equational reasoning *)

Notation "x 'QED'"         := (@eq_refl _ x)   (at level 100).
Notation "x '={' p '}=' q" := (eq_trans p q) 
                              (at level 101, right associativity, only parsing).

(* Notation for elements of sigT *)

Notation "'{|' x ';' p '|}'" := (existT _ x p).
Notation "x '.1'" := (projT1 x) (at level 1).
Notation "x '.2'" := (projT2 x) (at level 1).
