Set Warnings "-notation-overridden".
From Bonak.Lib Require Import Logic Tactics Equiv.
Import Logic.EqNotations.

Polymorphic Definition idToEquiv {A B: Type} (e: A = B): Equiv A B :=
  rew [Equiv A] e in idEquiv.

Polymorphic Axiom univalence: forall A B: Type, IsEquiv (@idToEquiv A B).

Polymorphic Definition uaEquiv (A B: Type): Equiv (A = B) (Equiv A B) :=
  {| eqvFun := @idToEquiv A B; eqvIsEquiv := univalence A B |}.

Polymorphic Definition ua {A B: Type} (e: Equiv A B): A = B := invEq (uaEquiv A B) e.

Polymorphic Lemma idToEquivRew {A B: Type} (e: A = B) (a: A):
  idToEquiv e a = rew [fun T: Type => T] e in a.
Proof.
  now destruct e.
Qed.

Polymorphic Lemma uaRew {A B: Type} (e: Equiv A B) (a: A):
  rew [fun T: Type => T] (ua e) in a = e a.
Proof.
  rewrite <- idToEquivRew.
  now exact (f_equal (fun E: Equiv A B => E a) (secEq (uaEquiv A B) e)).
Qed.
