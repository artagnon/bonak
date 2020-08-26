Require Import Interface.

Module LeYoneda <: Le.

Definition le n m := forall p, p <= n -> p <= m.
Infix "<=" := le : nat_scope.

Definition le_refl {n} : n <= n :=
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

Theorem le_dec {n m} : n <= S m -> {n = m} + {n <= S m}.
Admitted.

End LeYoneda.
