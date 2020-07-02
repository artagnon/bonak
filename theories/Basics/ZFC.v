From Coq Require Import ssreflect.
From Coq.Classes Require Import RelationClasses.
From Coq Require Import Setoid.

Parameter Obj : Set.
Parameter φ : Obj.
Parameter In : Obj -> Obj -> Prop.
Parameter Union : Obj -> Obj -> Obj.
Parameter Intersect : Obj -> Obj -> Obj.
Notation "x ∈ A" := (In x A) (at level 0).
Notation "x ∉ A" := (~(In x A)) (at level 0).
Notation "A ∪ B" := (Union A B) (at level 0).
Notation "A ∩ B" := (Intersect A B) (at level 0).
Notation "A ≠ B" := (~(A = B)) (at level 0).
Axiom LEM : forall (P : Prop), P \/ ~P.
Axiom eq : forall (A B : Obj), (A = B) <-> (forall x, x ∈ A <-> x ∈ B).
Axiom phi : forall x : Obj, x ∉ φ.
Axiom union : forall A B x : Obj, x ∈ (A ∪ B) <-> x ∈ A \/ x ∈ B.
Axiom intersect : forall A B x : Obj, x ∈ (A ∩ B) <-> x ∈ A /\ x ∈ B.

Lemma neq : forall (A B : Obj), ~(A = B) <-> exists x, (x ∈ A /\ x ∉ B) \/ (x ∉ A /\ x ∈ B).
Proof.
  firstorder.
Admitted.

Section Exercise1.
  Theorem eq_reflexive : forall (A : Obj), A = A.
  Proof.
    by move => A; apply eq => //=.
  Qed.

  Theorem eq_symmetric : forall (A B : Obj), A = B <-> B = A.
  Proof.
    move => A B; rewrite !eq.
    firstorder.
  Qed.

  Theorem eq_transitive : forall (A B C : Obj), A = B /\ B = C -> A = C.
  Proof.
    move => A B C; rewrite !eq.
    firstorder.
  Qed.
End Exercise1.

Section Exercise3.
  Theorem union_contract : forall A : Obj, A ∪ A = A.
  Proof.
    move => A; apply eq => x; rewrite union.
    by intuition.
  Qed.

  Theorem union_phi : forall A : Obj, A ∪ φ = A.
  Proof.
    move => A; apply eq => x; rewrite union.
    by intuition; apply phi in H0 => //=.
  Qed.
End Exercise3.
