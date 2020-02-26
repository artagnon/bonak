Require Import HoTT.

Axiom PropositionalProofIrrelevance : forall (P : Prop) (a b : P), a = b.

Theorem PropEquality (P : Prop) (a b : P) : a = b.
Proof.
  by apply PropositionalProofIrrelevance.
Qed.

Theorem hPropEquality (P : hProp) (a b : P) : a = b.
Proof.
  by apply path_ishprop.
Qed.
