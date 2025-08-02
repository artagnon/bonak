From Coq Require Import Eqdep_dec.
From Coq Require Import PeanoNat.
From Bonak Require Import Notation.

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

Lemma eq_O_contra {p}: p.+1 = O -> False.
  now auto.
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

Lemma le_succ_diag_l: forall n, n.+1 <~ n -> False.
Admitted.

Definition UIP_nat :=  Eqdep_dec.UIP_dec Nat.eq_dec.

Lemma leI_irrelevance {m n}: forall {H H': m <~ n}, H = H'.
Proof.
  generalize (eq_refl (S n)).
  generalize n at -1.
  induction (S n) as [|n0 IHn0]; try discriminate.
  clear n; intros n [= <-] H H'.
  pose (def_n2 := eq_refl n0).
  transitivity (eq_rect _ (fun n => m <~ n) H' _ def_n2).
    2: reflexivity.
  generalize def_n2; revert H H'.
  generalize n0 at 1 4 5 7; intros n1 H.
  destruct H as [|? H]; intros H'; destruct H' as [|? H'].
  + now intros def_n0; rewrite (UIP_nat _ _ def_n0 eq_refl).
  + intros def_n0; generalize H'; rewrite <- def_n0; intros le_mn0.
    now destruct (le_succ_diag_l _ le_mn0).
  + intros def_n0; generalize H; rewrite def_n0; intros le_mn0.
    now destruct (le_succ_diag_l _ le_mn0).
  + intros def_n0.
Admitted.
