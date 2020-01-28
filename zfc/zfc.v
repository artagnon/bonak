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
Axiom LEM : forall (P : Prop), P \/ ~P.
Axiom eq : forall (A B : Obj), (A = B) <-> (forall x, x ∈ A <-> x ∈ B).
Axiom phi : forall x : Obj, x ∉ φ.
Axiom union : forall A B x : Obj, x ∈ (A ∪ B) <-> x ∈ A \/ x ∈ B.
Axiom intersect : forall A B x : Obj, x ∈ (A ∩ B) <-> x ∈ A /\ x ∈ B.

Lemma implication_swap : forall A B, (A <-> B) <-> (B <-> A).
Proof.
  by intuition.
Qed.

Theorem eq_reflexive : forall (A : Obj), A = A.
Proof.
  intros.
  apply eq.
  by reflexivity.
Qed.

Theorem eq_symmetric : forall (A B : Obj), A = B <-> B = A.
Proof.
  intros.
  rewrite eq.
Abort.

Theorem eq_transitive : forall (A B C : Obj), A = B /\ B = C -> A = C.
Proof.
  intros.
  rewrite eq.
Abort.

