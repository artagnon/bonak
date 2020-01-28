From Coq Require Import ssreflect.
From Coq.Classes Require Import RelationClasses.

Parameter Obj : Set.
Axiom LEM : forall (P : Prop), P \/ ~P.
Parameter In : Obj -> Obj -> Prop.
Notation "x ∈ A" := (In x A) (at level 0).
Axiom eq : forall (A B : Obj), (A = B) <-> (forall x, x ∈ A <-> x ∈ B).

Lemma eq_reflexive : forall (A : Obj), A = A.
Proof.
  intros.
  apply eq.
  by reflexivity.
Qed.
