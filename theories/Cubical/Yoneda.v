Require Import Interface.

Module LeYoneda <: Le.

Definition le n m := forall p, p <= n -> p <= m.
Infix "<=" := le : nat_scope.

Definition le_refl {n} : n <= n :=
  fun _ => id.

Definition le_trans {n m p} (Hnm : n <= m) (Hmp : m <= p) : n <= p :=
  fun q (Hqn : Peano.le q n) => Hmp _ (Hnm _ Hqn).

Infix "↕" := le_trans (at level 30).

Definition le_S_up {n m} (Hnm : n <= m) : n <= S m :=
  fun Hnm => Hnm.
Defined.

Notation "↑ h" := (le_S_up h) (at level 40).

Definition le_S_down {n m} (Hnm : S n <= m) : n <= m :=
  fun Hnm => Hnm.
Defined.

Notation "⇓ p" := (le_S_down p) (at level 40).

Theorem le_trans_assoc {n m p q} (Hnm : n <= m) (Hmp : m <= p) (Hpq : p <= q) :
  Hnm ↕ (Hmp ↕ Hpq) = (Hnm ↕ Hmp) ↕ Hpq.
Proof.
reflexivity.
Qed.

End LeYoneda.
