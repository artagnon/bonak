Require Import HoTT.

Axiom PropositionalEquality : forall (P : Prop) (a b : P), a = b.

Theorem PropEquality (P : Prop) (a b : P) : a = b.
Proof.
  by apply PropositionalEquality.
Qed.

Theorem hPropEquality (P : hProp) (a b : P) : a = b.
Proof.
  by apply path_ishprop.
Qed.
