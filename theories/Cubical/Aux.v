Import Logic.EqNotations.
Require Import Yoneda.
Import LeYoneda.

Notation "( a ; b )" := (existT _ a b).
Notation "x .1" := (projT1 x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (projT2 x) (at level 1, left associativity, format "x .2").

Theorem le_irrelevance : forall {n m} (H H' : n <= m), H = H'.
Admitted.

Theorem thm1 : forall {n} (H : n <= S n), le_dec H = right (le_refl n).
Proof.
  intros; destruct (le_dec H) as [Heq|].
  - exfalso; apply n_Sn in Heq as [].
  - f_equal; apply le_irrelevance.
Defined.

Theorem thm1_symm : forall {n} (H : n <= S n), right (le_refl n) = le_dec H.
Proof.
  intros; symmetry; apply thm1.
Defined.

Theorem thm1_thm1_symm_id : forall {n} (H : n <= S n),
  eq_trans (thm1_symm H) (thm1 H) = eq_refl.
Proof.
  intros; unfold thm1_symm; destruct (thm1 H); trivial.
Defined.

Theorem proxy {A B} {P : B -> Type} (f : A -> B)
(Q : forall a, P (f a) -> Type) {x y} (e : f x = y)
(H : forall D : P y, Q x (rew <- e in D)) : (forall D : P (f x), Q x D).
Proof.
  destruct e; assumption.
Defined.

Theorem le_disjoint : forall n m, S n <= m -> m <= n -> False.
Admitted.

Theorem thm2 : forall {n n'} (H : n' <= S n) (H' : n' <= n),
le_dec H = right H'.
Proof.
  intros; destruct (le_dec H) as [->|].
  - exfalso; now apply le_disjoint in H'.
  - f_equal; apply le_irrelevance.
Defined.

Axiom UIP : forall A, forall {a : A} {b : A} (p : a = b) (q : a = b), p = q.
