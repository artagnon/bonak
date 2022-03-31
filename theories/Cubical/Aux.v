Require Import Arith.

Notation "( a ; b )" := (existT _ a b).
Notation "x .1" := (projT1 x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (projT2 x) (at level 1, left associativity, format "x .2").
Notation "x .+1" := (S x) (at level 1, left associativity, format "x .+1").
Notation "x .+2" := (S (S x)) (at level 1, left associativity, format "x .+2").
Notation "x .+3" := (S (S (S x))) (at level 1, left associativity, format "x .+3").

Lemma eq_pair {A B : Type} {u1 v1 : A} {u2 v2 : B} (p : u1 = v1) (q : u2 = v2):
  (u1, u2) = (v1, v2).
  now destruct p, q.
Qed.

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

(* An inductive definition of le *)
Reserved Infix "<~" (at level 70).
Inductive leI : nat -> nat -> Type :=
| leI_refl n : n <~ n
| leI_down {n p} : p.+1 <~ n -> p <~ n
where "n <~ m" := (leI n m) : nat_scope.

Lemma leI_up {n p : nat} : n <~ p -> n <~ p.+1.
  induction 1. constructor. now constructor. now constructor.
Defined.

Lemma leI_0 {p}: O <~ p.
  induction p. now constructor. now apply leI_up.
Defined.

Lemma leI_lower_both {n p}: p.+1 <~ n.+1 -> p <~ n.
  induction 1 using leI_rec with (P := fun p n _ => pred p <~ pred n).
  now constructor. destruct p0. now apply leI_0. now constructor.
Defined.

Lemma leI_raise_both {n p}: p <~ n -> p.+1 <~ n.+1.
  induction 1. now constructor. now constructor.
Defined.
