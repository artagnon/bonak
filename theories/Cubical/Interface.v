From Coq Require Import Arith.
Import Logic.EqNotations.

Module Type Le.

Axiom le : nat -> nat -> Type.
Infix "<=" := le.
Axiom le_refl : forall {n}, n <= n.
Axiom le_trans : forall {n m p}, n <= m -> m <= p -> n <= p.
Infix "↕" := le_trans (at level 30).
Axiom le_S_up : forall {n m}, n <= m -> n <= S m.
Notation "↑ h" := (le_S_up h) (at level 40).
Axiom le_S_down : forall {n m}, S n <= m -> n <= m.
Notation "⇓ p" := (le_S_down p) (at level 40).

Axiom le_trans_assoc : forall {n m p q} (Hnm : n <= m) (Hmp : m <= p)
(Hpq : p <= q), Hnm ↕ (Hmp ↕ Hpq) = (Hnm ↕ Hmp) ↕ Hpq.

End Le.
