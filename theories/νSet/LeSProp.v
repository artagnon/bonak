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
  now auto.
Qed.

Lemma leR_O {n}: leR O n.
  now auto.
Qed.

Lemma leR_trans {n m p} (Hnm: leR n m) (Hmp: leR m p): leR n p.
  revert n p Hnm Hmp. induction m, n, p. all: try now auto. simpl.
  now apply IHm.
Qed.

Infix "↕" := leR_trans (at level 45).

Lemma leR_up {n m} (Hnm: leR n m): leR n m.+1.
  revert m Hnm. induction n. now auto. destruct m. intros H.
  now apply leR_O_contra in H. now apply IHn.
Qed.

Notation "↑ h" := (leR_up h) (at level 40).

Lemma leR_down {n m} (Hnm: leR n.+1 m): leR n m.
  revert m Hnm. induction n. now auto. destruct m. intros H.
  now apply leR_O_contra in H. now apply IHn.
Qed.

Notation "↓ p" := (leR_down p) (at level 40).

Lemma leR_lower_both {n m} (Hnm: leR n.+1 m.+1): leR n m.
  now auto.
Qed.

Notation "⇓ p" := (leR_lower_both p) (at level 40).

Lemma leR_raise_both {n m} (Hnm: leR n m): leR n.+1 m.+1.
  now auto.
Qed.

Notation "⇑ p" := (leR_raise_both p) (at level 40).
Infix "<=" := leR: nat_scope.
