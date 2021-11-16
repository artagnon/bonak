From Coq Require Import Arith.
Import Logic.EqNotations.
Require Import Program.

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


Reserved Notation "x =_{ H } y" (at level 70, format "'[' x  '/ ' =_{ H }  '/' y ']'").
Inductive eq_over {A} (x: A) : forall {B} (y: B), A = B -> Prop :=
eq_over_refl : x =_{eq_refl} x
where "x =_{ H } y" := (eq_over x y H).

Ltac elim_ind_as p pat := elim_tac ltac:(fun p el => induction p as pat using el) p.
Ltac do_ind_as p pat := introduce p; (induction p as pat || elim_ind_as p pat).

Tactic Notation "dependent" "induction" ident(H) "as" simple_intropattern(pat) := do_depind ltac:(fun hyp => do_ind_as hyp pat) H.


Theorem proxy {A B} {P : B -> Type} (f : A -> B)
(Q : forall a, P (f a) -> Type) {x y} (e : f x = y)
(H : forall D : P y, Q x (rew <- e in D)) : (forall D : P (f x), Q x D).
Proof.
  now destruct e.
Defined.

Lemma applys_eq_init : forall (P Q: Prop),
  P = Q ->
  Q ->
  P.
Proof using. intros; now subst. Qed.

Lemma applys_eq_step_dep : forall B (P Q: (forall A, A -> B)) (T: Type),
  P = Q ->
  P T = Q T.
Proof using. intros; now subst. Qed.

Lemma applys_eq_step : forall A B (P Q: A -> B) x y,
  P = Q ->
  x = y ->
  P x = Q y.
Proof using. intros; now subst. Qed.

Ltac applys_eq_loop tt :=
  match goal with
  | |- ?P ?x =>
      first [ eapply applys_eq_step; [ applys_eq_loop tt | ]
            | eapply applys_eq_step_dep; applys_eq_loop tt ]
  | _ => reflexivity
  end.
