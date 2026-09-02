(** Arithmetic between [nat] using the SProp order [leR]. *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.Eqdep_dec Arith.Peano_dec.
From Bonak Require Import Notation LeSProp.

Set Keyed Unification.

Definition natUIP {a b: nat} (e e': a = b): e = e' :=
  UIP_dec PeanoNat.Nat.eq_dec e e'.

Lemma sub0r (m: nat): m - 0 = m.
Proof.
  now destruct m.
Qed.

Lemma subSuccL {r m: nat}: r <= m -> m.+1 - r = (m - r).+1.
Proof.
  revert m; induction r; intros m H.
  - now destruct m.
  - destruct m. destruct (leR_O_contra H). now exact (IHr m H).
Qed.

Lemma subPos {j m: nat}: j.+1 <= m -> m - j = (m - j.+1).+1.
Proof.
  revert m; induction j; intros m H.
  - destruct m. destruct (leR_O_contra H). cbn. now rewrite sub0r.
  - destruct m. destruct (leR_O_contra H). now exact (IHj m H).
Qed.

Lemma subSuccR (a b: nat): a - b.+1 = Nat.pred (a - b).
Proof.
  revert b; induction a; intros b.
  - now reflexivity.
  - destruct b. cbn. now rewrite sub0r. now exact (IHa b).
Qed.

Lemma addSubCancel {q m: nat}: q <= m -> q + (m - q) = m.
Proof.
  revert m; induction q; intros m H.
  - now exact (sub0r m).
  - destruct m. destruct (leR_O_contra H). cbn. now rewrite (IHq m H).
Qed.

Lemma subSplit {r q m: nat}: r <= q -> q <= m -> m - r = (q - r) + (m - q).
Proof.
  revert q m; induction r; intros q m Hr Hq.
  - rewrite 2 sub0r. now rewrite (addSubCancel Hq).
  - destruct q. destruct (leR_O_contra Hr).
    destruct m. destruct (leR_O_contra Hq).
    now exact (IHr q m Hr Hq).
Qed.

Lemma sub_leR (a b: nat): a - b <= a.
Proof.
  revert b; induction a; intros b.
  - now exact leR_O.
  - destruct b. exact leR_refl. now exact (↑ (IHa b)).
Qed.

Lemma subDiag (a: nat): a - a = 0.
Proof.
  induction a. reflexivity. now exact IHa.
Qed.

Lemma addSubCancelL (a b: nat): (a + b) - a = b.
Proof.
  induction a; cbn.
  - now apply sub0r.
  - now exact IHa.
Qed.

Lemma subSubCancel {dim L: nat}: dim <= L -> L - (L - dim) = dim.
Proof.
  revert L; induction dim; intros L H.
  - rewrite sub0r. now exact (subDiag L).
  - destruct L. destruct (leR_O_contra H).
    rewrite (subSuccL (sub_leR L dim)).
    now rewrite (IHdim L H).
Qed.
