From Coq Require Import Arith.
Import Logic.EqNotations.
Require Import Program.

Module Aux.
Notation "( a ; b )" := (existT _ a b).
Notation "x .1" := (projT1 x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (projT2 x) (at level 1, left associativity, format "x .2").
Notation "x .+1" := (S x) (at level 1, left associativity, format "x .+1").
Notation "x .+2" := (S (S x)) (at level 1, left associativity, format "x .+2").
Notation "x .+3" := (S (S (S x))) (at level 1, left associativity, format "x .+3").

(* Override rew notation to avoid showing terms in [...] *)
Notation "'rew' H 'in' H'" := (eq_rect _ _ H' _ H)
  (at level 10, H' at level 10,
    format "'[' 'rew'  H  in  '/' H' ']'").
Notation "'rew' <- H 'in' H'" := (eq_rect_r _ H' H)
  (at level 10, H' at level 10,
    format "'[' 'rew'  <-  H  in  '/' H' ']'").

(* eq_over: ... ={ H } ... *)
Reserved Notation "x =_{ H } y" (at level 70, format "'[' x  '/ ' =_{ H }  '/' y ']'").

Inductive eq_over {A} (x: A) : forall {B} (y: B), A = B -> Prop :=
eq_over_refl : x =_{eq_refl} x
where "x =_{ H } y" := (eq_over x y H).

End Aux.
