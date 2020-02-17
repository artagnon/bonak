Section Types.
  Theorem SetTypeCum : Set -> Type.
  Proof.
    auto.
  Qed.

  Theorem PropTypeCum : Prop -> Type.
  Proof.
    auto.
  Qed.

  Theorem SetPropDisjoint : Set -> Prop.
  Proof.
  Abort.

  Theorem SetPredicativity : forall (S : Set), S -> S.
  Proof.
    auto.
  Qed.
End Types.
