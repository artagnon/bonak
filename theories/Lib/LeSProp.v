Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.StrictProp.
From Bonak Require Import Notation.

(** False and True in SProp *)
Inductive SFalse: SProp :=.
Inductive STrue: SProp := sI.

(** A recursive definition of le *)
Fixpoint leR (n m: nat): SProp :=
  match n, m with
  | O, _ => STrue
  | S n, O => SFalse
  | S n, S m => leR n m
  end.

Lemma leR_refl {n}: leR n n.
Proof.
  now induction n.
Qed.

Lemma leR_O_contra {n}: leR n.+1 O -> SFalse.
Proof.
  now auto.
Qed.

Lemma leR_O {n}: leR O n.
Proof.
  now auto.
Qed.

Lemma leR_trans {n m p} (Hnm: leR n m) (Hmp: leR m p): leR n p.
Proof.
  revert n p Hnm Hmp. induction m, n, p. all: try now auto. simpl.
  now apply IHm.
Qed.

Infix "↕" := leR_trans (at level 45).

Lemma leR_up {n m} (Hnm: leR n m): leR n m.+1.
Proof.
  revert m Hnm. induction n. now auto. destruct m. intros H.
  now apply leR_O_contra in H. now apply IHn.
Qed.

Notation "↑ h" := (leR_up h) (at level 40).

Lemma leR_down {n m} (Hnm: leR n.+1 m): leR n m.
Proof.
  revert m Hnm. induction n. now auto. destruct m. intros H.
  now apply leR_O_contra in H. now apply IHn.
Qed.

Notation "↓ p" := (leR_down p) (at level 40).

Lemma leR_lower_both {n m} (Hnm: leR n.+1 m.+1): leR n m.
Proof.
  now auto.
Qed.

Notation "⇓ p" := (leR_lower_both p) (at level 40).

Lemma leR_raise_both {n m} (Hnm: leR n m): leR n.+1 m.+1.
Proof.
  now auto.
Qed.

Notation "⇑ p" := (leR_raise_both p) (at level 40).
Infix "<=" := leR: nat_scope.

Definition leR_eq {a b n: nat} (e: a = b): a <= n -> b <= n :=
  match e with eq_refl => fun H => H end.

Definition leR_eq_r {a n n': nat} (e: n = n'): a <= n -> a <= n' :=
  match e with eq_refl => fun H => H end.

Definition leR_add_shift {q p n: nat}: q + p.+1 <= n -> q.+1 + p <= n :=
  leR_eq (eq_sym (plus_n_Sm q p)).

Fixpoint leR_add_l (q: nat) {p: nat}: p <= q + p :=
  match q with
  | 0 => leR_refl
  | S q => ↑ (leR_add_l q)
  end.

Fixpoint leR_add_r (p L: nat) {struct L}: p <= p + L :=
  match L with
  | 0 => leR_eq_r (plus_n_O p) leR_refl
  | S L => leR_eq_r (plus_n_Sm p L) (↑ (leR_add_r p L))
  end.
