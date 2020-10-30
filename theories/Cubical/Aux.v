Require Import Yoneda.
Import LeYoneda.

Notation "l '.1'" := (projT1 l) (at level 40).
Notation "l '.2'" := (projT2 l) (at level 40).

Theorem le_irrelevance : forall {n m} (H H' : n <= m), H = H'.
Admitted.

Theorem thm1 : forall {n} (H : n <= S n), le_dec H = right (le_refl n).
Proof.
intros.
destruct (le_dec H) as [Heq|].
- exfalso. apply n_Sn in Heq as [].
- f_equal.
  apply le_irrelevance.
Defined.

Theorem le_disjoint : forall n m, S n <= m -> m <= n -> False.
Admitted.

Theorem thm2 : forall {n n'} (H:n' <= S n) (H':n' <= n), le_dec H = right H'.
Proof.
intros.
destruct (le_dec H) as [->|].
- exfalso.
  now apply le_disjoint in H'.
- f_equal.
  apply le_irrelevance.
Defined.
