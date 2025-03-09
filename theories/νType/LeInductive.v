From Bonak Require Import Notation.

Set Warnings "-notation-overridden".
Reserved Infix "<=" (at level 70).
Inductive lePeano p: nat -> Type :=
  | le_n: p <= p
  | le_S {n}: p <= n -> p <= n.+1
where "p <= n" := (lePeano p n): nat_scope.

Arguments le_S {p n} H.

(** An inductive definition of le *)
Reserved Infix "<~" (at level 70).
Inductive leI n: nat -> Type :=
| leI_refl: n <~ n
| leI_down {p}: p.+1 <~ n -> p <~ n
where "p <~ n" := (leI n p): nat_scope.

Arguments leI_down {n p} H.

Lemma leI_up {p n}: p <~ n -> p <~ n.+1.
  induction 1. constructor. now constructor. now constructor.
Defined.

Lemma leI_O {p}: O <~ p.
  induction p. now constructor. now apply leI_up.
Defined.

Lemma le_O {p}: O <= p.
  induction p. now constructor. now constructor.
Defined.

Lemma le_O_contra {p}: p.+1 <= O -> False.
  destruct p. now auto. now auto.
Defined.

Lemma eq_O_contra {p}: p.+1 = O -> False.
  now auto.
Defined.

Lemma le_O_eq {p}: p <= 0 -> p = 0.
  intro H. destruct p. now trivial. exfalso. now apply le_O_contra in H.
Defined.

Lemma le_down {p n}: p.+1 <= n -> p <= n.
  induction 1. constructor; now constructor. now constructor.
Defined.

Lemma le_up {p n}: p <= n -> p <= n.+1.
  induction 1. constructor; now constructor. now constructor.
Defined.

(* Lemma le_lower_both {p n}: p.+1 <= n.+1 -> p <= n.
  induction 1. apply le_down. now constructor. admit. apply le_up in IHn. now intros _.
Defined. *)

Lemma leI_le_conversion {p n}: p <~ n -> p <= n.
  induction 1. now constructor. now apply le_down.
Defined.

Lemma le_leI_conversion {p n}: p <= n -> p <~ n.
  induction 1. now constructor. now apply leI_up.
Defined.

Lemma le_O_eq' {p}: p = 0 -> p <= 0.
  intro H. destruct p. now constructor. exfalso. now apply eq_O_contra in H.
Defined.

Lemma leI_O_eq {p}: p <~ 0 -> p = 0.
  intro H. apply leI_le_conversion in H. now apply le_O_eq.
Defined.

Lemma leI_O_eq' {p}: p = 0 -> p <~ 0.
  intro H. apply le_leI_conversion. now apply le_O_eq'.
Defined.

Lemma leI_O_contra {n}: n.+1 <~ O -> False.
  intro H. now apply leI_le_conversion in H.
Defined.

Lemma leI_lower_both {n p}: p.+1 <~ n.+1 -> p <~ n.
  intro H. change p with (pred (S p)). induction H.
  now constructor. destruct p0. now apply leI_O. now constructor.
Defined.

Lemma leI_raise_both {n p}: p <~ n -> p.+1 <~ n.+1.
  induction 1. now constructor. now constructor.
Defined.

Lemma leI_trans {n p q}: p <~ n -> n <~ q -> p <~ q.
Proof.
  intros H1 H2. induction H1. now easy. now constructor.
Defined.

Lemma leI_invert {P : forall p n, p <~ n -> Type}
  {Q: forall p, P p p (leI_refl p)}
  {R: forall p n (Hp: p.+1 <~ n.+1), P p.+1 n.+1 Hp -> P p n.+1 (leI_down Hp)}
  {p n} (Hp: p <~ n): P p n Hp.
Proof.
  induction Hp.
  - apply Q.
  - destruct n. destruct (leI_O_contra Hp). apply R, IHHp.
Defined.

Section leI_rectS_principle.
  Variable n: nat.
  Variable p: nat.
  Hypothesis P: forall p, p.+1 <~ n.+1 -> Type.
  Hypothesis Q: P n (leI_refl n.+1).
  Hypothesis R: forall p (Hp : p.+2 <~ n.+1), P p.+1 Hp -> P p (leI_down Hp).
  Lemma leI_rectS (Hp : p.+1 <~ n.+1): P p Hp.
  Proof.
    change (match p.+1 as p' return p' <~ n.+1 -> Type with
    | 0 => fun _ => True
    | p.+1 => fun Hp => P p Hp
    end Hp). induction Hp. now easy. destruct p0. now easy. now apply R.
  Defined.
End leI_rectS_principle.

Lemma leI_raise_lower_cancel {n p} {Hp: p.+1 <~ n.+1}:
  leI_raise_both (leI_lower_both Hp) = Hp.
  induction Hp using leI_rectS. now easy.
  change (leI_lower_both (leI_down ?x)) with (leI_down (leI_lower_both x)).
  change (leI_raise_both (leI_down ?x)) with (leI_down (leI_raise_both x)).
  now f_equal.
Defined.
