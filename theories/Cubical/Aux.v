Import Logic.EqNotations.
Require Import Yoneda.
Import LeYoneda.

Notation "( a ; b )" := (existT _ a b).
Notation "x .1" := (projT1 x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (projT2 x) (at level 1, left associativity, format "x .2").
Notation "x .+1" := (S x) (at level 1, left associativity, format "x .+1").
Notation "x .+2" := (S (S x)) (at level 1, left associativity, format "x .+2").

Reserved Notation "x =_{ H } y" (at level 70).
Inductive eq_over {A} (x : A) : forall {B} (y : B), A = B -> Prop :=
eq_over_refl : x =_{eq_refl} x
where "x =_{ H } y" := (eq_over x y H).

Theorem proxy {A B} {P : B -> Type} (f : A -> B)
(Q : forall a, P (f a) -> Type) {x y} (e : f x = y)
(H : forall D : P y, Q x (rew <- e in D)) : (forall D : P (f x), Q x D).
Proof.
  destruct e; assumption.
Defined.

Theorem le_disjoint : forall n m, S n <= m -> m <= n -> False.
Admitted.

Axiom UIP : forall A, forall {a : A} {b : A} (p : a = b) (q : a = b), p = q.
