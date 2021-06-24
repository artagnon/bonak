Require Import Interface.
Require Import Arith.
Require Import RelationClasses.

Module LeYoneda.

Inductive le' (n : nat) : nat -> SProp :=
  | le_refl' : n <= n
  | le_S_up' : forall (m : nat), n <= m -> n <= S m
  where "n <= m" := (le' n m) : nat_scope.

Ltac reflexivity' := apply le_refl' || reflexivity.
Ltac reflexivity := reflexivity'.

Definition le n m := forall p, p <= n -> p <= m.
Infix "<=" := le : nat_scope.

Inductive eqsprop {A : SProp} (x : A) : A -> Prop := eqsprop_refl : eqsprop x x.
Infix "=S" := eqsprop (at level 70) : type_scope.

Theorem le_irrelevance : forall {n m} (H H' : n <= m), H =S H'.
  reflexivity.
Defined.

Definition le_refl n : n <= n :=
  fun _ x => x.

Definition le_trans {n m p} (Hnm : n <= m) (Hmp : m <= p) : n <= p :=
  fun q (Hqn : le' q n) => Hmp _ (Hnm _ Hqn).

Infix "↕" := le_trans (at level 45).

Theorem le_S_up {n m} (Hnm : n <= m) : n <= S m.
  unfold le.
  intros p Hpn.
  apply le_S_up'.
  apply Hnm.
  assumption.
Defined.

Notation "↑ h" := (le_S_up h) (at level 40).

Theorem le_S_down {n m} (Hnm : S n <= m) : n <= m.
  unfold le.
  intros p Hpn.
  apply Hnm.
  apply le_S_up'.
  assumption.
Defined.

Notation "↓ p" := (le_S_down p) (at level 40).

Theorem le_S_both {n m} (Hnm : S n <= S m) : n <= m.
  unfold le.
  intros p Hpn.
Admitted.

Notation "⇓ p" := (le_S_both p) (at level 40).

Theorem raise_S_both {n m} (Hnm : n <= m) : S n <= S m.
  unfold le.
  intros p Hpn.
Admitted.

Notation "⇑ p" := (raise_S_both p) (at level 40).

Theorem le_trans_assoc {n m p q} (Hnm : n <= m) (Hmp : m <= p) (Hpq : p <= q) :
  Hnm ↕ (Hmp ↕ Hpq) =S (Hnm ↕ Hmp) ↕ Hpq.
Proof.
  reflexivity.
Defined.

Theorem le_trans_comm {n m p} (Hnm : n <= m) (Hmp : m <= p) :
  (Hnm ↕ ↑ Hmp) =S ↑ (Hnm ↕ Hmp).
Proof.
  reflexivity.
Defined.

Theorem le_trans_comm2 {m p} (Hmm : m <= m) (Hmp : S m <= S p) :
  (Hmm ↕ ↓ Hmp) =S ↑ (⇓ Hmp).
Proof.
  reflexivity.
Defined.

Theorem le_trans_comm3 {n m} (Hmn : S (S n) <= S m) : ⇓ (↓ Hmn) =S ↓ (⇓ Hmn).
Proof.
  reflexivity.
Defined.

Theorem le_trans_comm4 {n m p} (Hmn : S n <= S m) (Hmp : S m <= S p) :
  ⇓ (Hmn ↕ Hmp) =S (⇓ Hmn) ↕ (⇓ Hmp).
  reflexivity.
Defined.

Theorem le_trans_comm5 {n m p} (Hmn : n <= m) (Hmp : m <= p) :
  ⇑ (Hmn ↕ Hmp) =S (⇑ Hmn) ↕ (⇑ Hmp).
  reflexivity.
Defined.

Theorem le_trans_comm6 {n m} (Hmn : n <= m) : (⇓ ⇑ Hmn) =S Hmn.
  reflexivity.
Defined.

Theorem le_trans_comm7 {n m p} (Hmn : S n <= S m) (Hmp : S m <= p) :
  ↓ (Hmn ↕ Hmp) =S (⇓ Hmn) ↕ (↓ Hmp).
  reflexivity.
Defined.

End LeYoneda.
