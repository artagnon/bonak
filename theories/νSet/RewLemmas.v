(** A few rewriting lemmas not in the standard library *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet Notation.

Lemma rew_existT_curried {A x} {P: A -> Type} {Q: {a &T P a} -> Type}
   {y} {H: x = y}
   {u: P x} {v: Q (x; u)}
   {u': P y} {v': Q (y; u')}
   {Hu: rew H in u = u'} {Hv: rew (=H; Hu) in v = v'}:
   rew [fun x => {a: P x &T Q (x; a)}] H in (u; v) = (u'; v').
Proof.
   now destruct Hu, Hv, H.
Qed.

Lemma rew_permute_ll_hset: forall (A: Type) (P Q: A -> HSet) (x y: A)
  (H: forall z: A, P z = Q z) (H': x = y) (a: P x),
  rew [Dom] H y in rew [P] H' in a = rew [Q] H' in rew [Dom] H x in a.
Proof.
  now destruct H'.
Defined.

Lemma rew_swap: forall A (P: A -> Type) a b (H: a = b) (x: P a) (y: P b),
  x = rew <- H in y <-> rew H in x = y.
Proof.
  now destruct H.
Qed.

Lemma rew_app_rl A (P: A -> Type) (x y: A) (H H': x = y) (a: P x) :
  H = H' -> rew <- [P] H in rew [P] H' in a = a.
Proof.
  intros * ->. now destruct H'.
Qed.

Lemma map_subst_app {A B} {x y} {𝛉: A} (H: x = y :> B) (P: A -> B -> Type)
  (f: forall 𝛉, P 𝛉 x):
  rew [P 𝛉] H in f 𝛉 = (rew [fun x => forall 𝛉, P 𝛉 x] H in f) 𝛉.
Proof.
  now destruct H.
Qed.
