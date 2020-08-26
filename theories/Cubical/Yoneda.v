Require Import Interface.
Require Import Arith.

Module LeYoneda <: Le.

Definition le n m := forall p, p <= n -> p <= m.
Infix "<=" := le : nat_scope.

Definition le_refl n : n <= n :=
  fun _ => id.

Definition le_trans {n m p} (Hnm : n <= m) (Hmp : m <= p) : n <= p :=
  fun q (Hqn : Peano.le q n) => Hmp _ (Hnm _ Hqn).

Infix "↕" := le_trans (at level 30).

Theorem le_S_up {n m} (Hnm : n <= m) : n <= S m.
  unfold le.
  intros p Hpn.
  apply (Peano.le_S p m).
  apply Hnm.
  auto.
Defined.

Notation "↑ h" := (le_S_up h) (at level 40).

Theorem le_S_down {n m} (Hnm : S n <= m) : n <= m.
  unfold le.
  intros p Hpn.
  apply Hnm.
  apply Peano.le_S.
  auto.
Defined.

Notation "⇓ p" := (le_S_down p) (at level 40).

Theorem le_trans_assoc {n m p q} (Hnm : n <= m) (Hmp : m <= p) (Hpq : p <= q) :
  Hnm ↕ (Hmp ↕ Hpq) = (Hnm ↕ Hmp) ↕ Hpq.
Proof.
reflexivity.
Qed.

Theorem le_trans_comm {n m p} (Hnm : n <= m) (Hmp : m <= p) :
  (Hnm ↕ ↑ Hmp) = ↑ (Hnm ↕ Hmp).
Proof.
reflexivity.
Defined.

Theorem le1 {n m} : Peano.le n m -> n <= m.
Proof.
intros H p Hp.
eapply PeanoNat.Nat.le_trans; eassumption.
Defined.

Theorem le2 {n m} : n <= m -> Peano.le n m.
Proof.
intros H; apply H, Peano.le_n.
Defined.

Theorem le_dec {n m} : n <= S m -> {n = S m} + {n <= m}.
Proof.
intros.
destruct (le_lt_eq_dec n (S m)).
apply le2, H.
right; apply le_S_n in l. apply (le1 l).
left; apply e.
Defined.

Theorem le_discr {n} : S n <= 0 -> forall {A}, A.
Proof.
intros H%le2.
exfalso.
eapply Nat.nle_succ_0. eauto.
Defined.

End LeYoneda.
