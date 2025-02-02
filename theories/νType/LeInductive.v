From Bonak Require Import Notation.

(** An inductive definition of le *)
Reserved Infix "<~" (at level 70).
Inductive leI n: nat -> Type :=
| leI_refl: n <~ n
| leI_down {p}: p.+1 <~ n -> p <~ n
where "p <~ n" := (leI n p): nat_scope.

Arguments leI_down {n p} H.

Lemma leI_up {n p}: n <~ p -> n <~ p.+1.
  induction 1. constructor. now constructor. now constructor.
Defined.

Lemma leI_O {p}: O <~ p.
  induction p. now constructor. now apply leI_up.
Defined.

Lemma leI_O_contra {n}: n.+1 <~ O -> False.
  intro H.
Admitted.

Lemma leI_lower_both {n p}: p.+1 <~ n.+1 -> p <~ n.
  intro H. change p with (pred (S p)).
  induction H.
  now constructor. destruct p0. now apply leI_O. now constructor.
Defined.

Lemma leI_raise_both {n p}: p <~ n -> p.+1 <~ n.+1.
  induction 1. now constructor. now constructor.
Defined.

Lemma leI_trans {n p q}: p <~ n -> n <~ q -> p <~ q.
Proof.
  intros H1 H2. induction H1. now easy. now constructor.
Defined.

Lemma leI_invert : forall P : forall p n : nat, p <~ n -> Type,
       (forall p : nat, P p p (leI_refl p)) ->
       (forall (p n : nat) (l : p.+1 <~ n.+1),
        P p.+1 n.+1 l -> P p n.+1 (leI_down l)) ->
       forall (p n : nat) (l : p <~ n), P p n l.
Proof.
intros P H H0 p n.
induction l.
- apply H.
- destruct n. destruct (leI_O_contra l). apply H0, IHl.
Defined.
