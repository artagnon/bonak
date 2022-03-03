Require Import Arith.

Notation "( a ; b )" := (existT _ a b).
Notation "x .1" := (projT1 x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (projT2 x) (at level 1, left associativity, format "x .2").
Notation "x .+1" := (S x) (at level 1, left associativity, format "x .+1").
Notation "x .+2" := (S (S x)) (at level 1, left associativity, format "x .+2").
Notation "x .+3" := (S (S (S x))) (at level 1, left associativity, format "x .+3").

(* Notations for rew *)
Notation "'rew' [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10,
    format "'[' 'rew'  [ P ]  '/    ' H  in  '/' H' ']'").
Notation "'rew' <- [ P ] H 'in' H'" := (eq_rect_r P H' H)
    (at level 10, H' at level 10,
    format "'[' 'rew'  <-  [ P ]  '/    ' H  in  '/' H' ']'").

(* eq_over: ... ={ H } ... *)
Reserved Notation "x =_{ H } y" (at level 70, format "'[' x  '/ ' =_{ H }  '/' y ']'").

Inductive eq_over {A} (x: A) : forall {B} (y: B), A = B -> Prop :=
eq_over_refl : x =_{eq_refl} x
where "x =_{ H } y" := (eq_over x y H).

(* eq_existT_curried *)
Notation "(= u ; v )" := (eq_existT_curried u v)
(at level 0, format "(= u ;  '/  ' v )").

(* eq_trans, eq_sym *)
Infix "•" := eq_trans (at level 65, left associativity).
Notation "[ x ⇒ f ] e" := (f_equal (fun x => f) e)
(at level 60, left associativity).
Notation "x ^" := (eq_sym x) (at level 55, left associativity, format "x ^").
