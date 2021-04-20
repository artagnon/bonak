Import Logic.EqNotations.
Require Import Yoneda.
Import LeYoneda.

Notation "( a ; b )" := (existT _ a b).
Notation "x .1" := (projT1 x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (projT2 x) (at level 1, left associativity, format "x .2").
Notation "x .+1" := (S x) (at level 1, left associativity, format "x .+1").
Notation "x .+2" := (S (S x)) (at level 1, left associativity, format "x .+2").
Notation "x .+3" := (S (S (S x))) (at level 1, left associativity, format "x .+3").

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

Lemma applys_eq_init : forall (P Q:Prop),
  P = Q ->
  Q ->
  P.
Proof using. intros. subst. auto. Qed.

Lemma applys_eq_step_dep : forall B (P Q: (forall A, A->B)) (T:Type),
  P = Q ->
  P T = Q T.
Proof using. intros. subst. auto. Qed.

Lemma applys_eq_step : forall A B (P Q:A->B) x y,
  P = Q ->
  x = y ->
  P x = Q y.
Proof using. intros. subst. auto. Qed.

Ltac applys_eq_loop tt :=
  match goal with
  | |- ?P ?x =>
      first [ eapply applys_eq_step; [ applys_eq_loop tt | ]
            | eapply applys_eq_step_dep; applys_eq_loop tt ]
  | _ => reflexivity
  end.

Ltac applys_eq_core H :=
  eapply applys_eq_init;
  [ applys_eq_loop tt | apply H ];
  try ( reflexivity || apply le_irrelevance ).

Tactic Notation "applys_eq" constr(H) :=
  applys_eq_core H.
