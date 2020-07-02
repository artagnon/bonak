From Coq Require Import Logic.StrictProp ssreflect.

Section ProofRelevance.
  (* Inhabitants of Prop are proof-relevant propositions. *)
  Theorem PropRel (P : Prop) (x y : P): x = y.
  Proof.
  Abort.

  Theorem PropRefl (P : Prop) (x : P): x = x.
    exact eq_refl.
  Qed.

  Inductive eq (A : Type) (x : A) : A -> Prop :=
    eq_refl : eq A x x.

  Set Allow StrictProp.

  Theorem SPropToProp : SProp -> Prop.
  Proof.
    by intros x; exact x.
  Abort. (* Type-check fails at Qed.
          * SProp is not convertible to Prop. *)

  (* Indeed, we cannot define a function from SProp -> Prop *)
  Fail Definition SPropToProp' (x : SProp) : Prop :=
  match x with _ => x end.

  (* Inhabitants of SProp are: sUnit, sEmpty, and sProposition.
   * All inhabitants of sProposition are interconvertible,
   * thanks to inelegant hard-coded tagging:
   * this explains why 'reflexivity' succeeds. *)
  Theorem SPropIrr (P : SProp) (x y : P) : x = y.
  Proof.
    by reflexivity.
  Abort. (* Type-check fails at Qed.
          * (=) : forall A, A -> A -> Type, but we want to return an SProp. *)
End ProofRelevance.
