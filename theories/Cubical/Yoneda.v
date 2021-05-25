Require Import Interface.
Require Import Arith.

Module LeYoneda <: Le.

Definition le n m := forall p, p <= n -> p <= m.
Infix "<=" := le : nat_scope.

Theorem le_irrelevance : forall {n m} (H H' : n <= m), H = H'.
Admitted.

Definition le_refl n : n <= n :=
  fun _ x => x.

Definition le_trans {n m p} (Hnm : n <= m) (Hmp : m <= p) : n <= p :=
  fun q (Hqn : Peano.le q n) => Hmp _ (Hnm _ Hqn).

Infix "↕" := le_trans (at level 45).

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

Notation "↓ p" := (le_S_down p) (at level 40).

Theorem le_S_both {n m} (Hmn : S n <= S m) : n <= m.
  unfold le.
  intros p Hpn.
  apply Peano.le_S_n.
  apply Hmn.
  auto.
  apply Peano.le_n_S.
  now apply Hpn.
Defined.

Notation "⇓ p" := (le_S_both p) (at level 40).

Theorem raise_S_both {n m} (Hmn : n <= m) : S n <= S m.
  unfold le.
  intros p Hpn.
Admitted.

Notation "⇑ p" := (raise_S_both p) (at level 40).

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

Theorem le_trans_comm2 {m p} (Hmm : m <= m) (Hmp : S m <= S p) :
  (Hmm ↕ ↓ Hmp) = ↑ (⇓ Hmp).
Proof.
  now apply le_irrelevance.
Defined.

Theorem le_trans_comm3 {n m} (Hmn : S (S n) <= S m) : ⇓ (↓ Hmn) = ↓ (⇓ Hmn).
Proof.
  now apply le_irrelevance.
Defined.

Theorem le_trans_comm4 {n m p} (Hmn : S n <= S m) (Hmp : S m <= S p):
  ⇓ (Hmn ↕ Hmp) = (⇓ Hmn) ↕ (⇓ Hmp).

Theorem le1 {n m} : Peano.le n m -> n <= m.
Proof.
  intros H p Hp.
  eapply PeanoNat.Nat.le_trans; eassumption.
Defined.

Theorem le2 {n m} : n <= m -> Peano.le n m.
Proof.
  intros H; apply H, Peano.le_n.
Defined.

Theorem le_discr {n} : S n <= 0 -> forall {A}, A.
Proof.
  intros H%le2.
  exfalso.
  eapply Nat.nle_succ_0. eauto.
Defined.

End LeYoneda.
