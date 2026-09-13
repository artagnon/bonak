(** Equality of presheaves equipped with degeneracies. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak Require Import SigT RewLemmas HSet LeSProp Notation νSet.Layer
  Funext Univalence Equiv.PresheafEquiv.
From Bonak.Lib Require Import Equiv.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module Type PshEqSig (A: LayerSig).
Include Bonak.Equiv.PresheafEquiv.PresheafEquiv A.
End PshEqSig.

Module PresheafEquivOn (A: LayerSig) (E: PshEqSig A).
Import A.

Module Export PshEq := E.

Definition Presheaf: Type := { psh: PshEq.Psh.Presheaf &T PresheafDgn psh }.

Record PresheafEquiv (X Y: Presheaf) := {
  underlyingEquiv: PshEq.PresheafEquiv X.1 Y.1;
  DgnEquiv n i (Hi: i <= n) (x: X.1.(F0) n):
    underlyingEquiv.(F0Equiv _ _) n.+1 (X.2.(Dgn _) n i Hi x) =
    Y.2.(Dgn _) n i Hi (underlyingEquiv.(F0Equiv _ _) n x)
}.

Lemma structureEqIntro {psh: PshEq.Psh.Presheaf} (R S: PresheafDgn psh)
  (e: R.(Dgn _) = S.(Dgn _)): R = S.
Proof.
  destruct R as [d ri rid rs rr], S as [d' si sid ss sr]; cbn in e.
  destruct e.
  f_equal;
    repeat first [apply functional_extensionality_dep_good; intro
                 |apply spropFunext; intro];
    apply (psh.(F0) _).(UIP).
Qed.

Lemma presheafEqIntro (X Y: Presheaf)
  (e0: X.1.(F0) = Y.1.(F0))
  (ef: rew [fun F: nat -> HSet =>
         forall n i (Hi: i <= n) (ε: arity), F n.+1 -> F n] e0 in
       X.1.(Face) = Y.1.(Face))
  (ed: rew [fun F: nat -> HSet =>
         forall n i (Hi: i <= n), F n -> F n.+1] e0 in
       X.2.(Dgn _) = Y.2.(Dgn _)): X = Y.
Proof.
  destruct X as [[F f c] R], Y as [[F' f' c'] S]; cbn in e0, ef, ed.
  destruct e0; cbn in ef, ed. destruct ef.
  assert (ec: c = c').
  { repeat first [apply functional_extensionality_dep_good; intro
                 |apply spropFunext; intro].
    apply (F _).(UIP). }
  destruct ec.
  now destruct (structureEqIntro R S ed).
Qed.

Lemma rew_dgn_app {F G: nat -> HSet} (e: F = G)
  (d: forall n i (Hi: i <= n), F n -> F n.+1)
  n i (Hi: i <= n) (x: G n):
  (rew [fun F: nat -> HSet =>
     forall n i (Hi: i <= n), F n -> F n.+1] e in d) n i Hi x =
  rew [fun F: nat -> HSet => (F n.+1).(Dom)] e in
    d n i Hi (rew <- [fun F: nat -> HSet => (F n).(Dom)] e in x).
Proof.
  now destruct e.
Qed.

Lemma presheafEquivEq {X Y: Presheaf} (E: PresheafEquiv X Y):
  X = Y.
Proof.
  pose (e := E.(underlyingEquiv _ _)).
  apply (presheafEqIntro X Y
    (functional_extensionality_dep_good _ _
      (fun n => hsetEq (e.(F0Equiv _ _) n)))).
  - exact (PshEq.presheafFaceEquivEq e).
  - apply functional_extensionality_dep_good; intro n.
    apply functional_extensionality_dep_good; intro i.
    apply spropFunext; intro Hi.
    apply functional_extensionality_dep_good; intro y.
    rewrite rew_dgn_app.
    unfold eq_rect_r.
    rewrite (rew_map (fun h: HSet => h.(Dom)) (fun F: nat -> HSet => F n.+1)).
    rewrite (rew_map (fun h: HSet => h.(Dom)) (fun F: nat -> HSet => F n)).
    rewrite <- eq_sym_f_equal.
    rewrite 2 funExtBetaHSet.
    cbv beta.
    rewrite hsetEqRew, hsetEqRewSym.
    refine (E.(DgnEquiv _ _) n i Hi (invEq (e.(F0Equiv _ _) n) y) • _).
    now exact (f_equal (Y.2.(Dgn _) n i Hi)
      (secEq (e.(F0Equiv _ _) n) y)).
Qed.

End PresheafEquivOn.

Module PresheafEquiv (A: LayerSig).
Module Base := Bonak.Equiv.PresheafEquiv.PresheafEquiv A.
Include PresheafEquivOn A Base.
End PresheafEquiv.

Module PresheafEquivSimplicial := PresheafEquiv SimplicialLayer.
Module PresheafEquivCubical := PresheafEquiv CubicalLayer.
