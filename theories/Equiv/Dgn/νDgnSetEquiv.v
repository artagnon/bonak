(** Equality of degeneracy layers and of coherent towers of prefixes. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak Require Import SigT HSet LeSProp Notation RewLemmas Funext
  νSet.Layer Equiv.Dgn.PresheafRoundtrip Limit.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module νDgnSetEquiv (A: LayerSig).
Import A.
Module Export PshRoundtrip := Bonak.Equiv.Dgn.PresheafRoundtrip.PresheafRoundtrip A.

Lemma cohAboveAbovePaintingIrrel {p k} (deps: DepsReflCohsSup p k)
  (extra: DepsReflCohsSupExtension p k deps)
  (frames: mkCohReflAboveAboveFrameTypes deps)
  (a b: mkCohReflAboveAbovePaintingTypes deps extra frames): a = b.
Proof.
  revert k deps extra frames a b; induction p; intros k deps extra frames a b.
  - exact (hunit_ext _ _).
  - destruct a as [a a'], b as [b b'].
    pose proof (IHp _ _ _ _ a b) as e. destruct e.
    apply (f_equal (fun c => (a; c))).
    repeat first [apply functional_extensionality_dep_good; intro
                 |apply spropFunext; intro].
    apply (mkPainting (mkExtraDeps (CohsExtOfReflCohsSup deps)) _).(UIP).
Qed.

Lemma dgnLayerEq {p} (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (D: DgnData C E)
  (a b: {L: dgnHasReflFromData C E E' D &T dgnCohLFromData C E E' D L})
  (H: forall i (Hi: i <= p) d c, a.1 i Hi d c = b.1 i Hi d c): a = b.
Proof.
  assert (e: a.1 = b.1).
  { apply functional_extensionality_dep_good; intro i.
    apply spropFunext; intro Hi.
    apply functional_extensionality_dep_good; intro d.
    apply functional_extensionality_dep_good; intro c. exact (H i Hi d c). }
  apply (eq_existT_curried e).
  apply cohAboveAbovePaintingIrrel.
Qed.

Definition DgnStepBase n: Type := {Y: DgnPrefix n &T νFillerType Y.1}.

Definition dgnLayerType n (Z: DgnStepBase n): Type :=
  (νDgnSetAt n).(dgnStepType) Z.1.1 Z.1.2 Z.2.

Definition dgnExtendEq {n} {X Y: DgnPrefix n} (e: X = Y)
  {a: dgnIncrType X} {b: dgnIncrType Y}
  (ef: rew [fun Z: DgnPrefix n => νFillerType Z.1] e in a.1 = b.1)
  (el: rew [dgnLayerType n] (eq_existT_curried e ef : ((X; a.1): DgnStepBase n) = (Y; b.1)) in (a.2: dgnLayerType n (X; a.1)) = b.2):
  dgnExtend X a = dgnExtend Y b.
Proof.
  destruct e, a as [F L], b as [G M]; cbn in ef, el.
  destruct ef; cbn in el. destruct el. reflexivity.
Defined.

Lemma dgnExtendEqBond {n} {X Y: DgnPrefix n} (e: X = Y)
  {a: dgnIncrType X} {b: dgnIncrType Y}
  (ef: rew [fun Z: DgnPrefix n => νFillerType Z.1] e in a.1 = b.1)
  (el: rew [dgnLayerType n] (eq_existT_curried e ef : ((X; a.1): DgnStepBase n) = (Y; b.1)) in (a.2: dgnLayerType n (X; a.1)) = b.2):
  f_equal (@dgnBond n) (dgnExtendEq e ef el) = e.
Proof.
  destruct e, a as [F L], b as [G M]; cbn in ef, el.
  destruct ef; cbn in el. destruct el. reflexivity.
Qed.

Lemma dgnExtendEqUnderlying {n} {X Y: DgnPrefix n} (e: X = Y)
  {a: dgnIncrType X} {b: dgnIncrType Y}
  (ef: rew [fun Z: DgnPrefix n => νFillerType Z.1] e in a.1 = b.1)
  (el: rew [dgnLayerType n] (eq_existT_curried e ef : ((X; a.1): DgnStepBase n) = (Y; b.1)) in (a.2: dgnLayerType n (X; a.1)) = b.2):
  f_equal (fun Z: DgnPrefix n.+1 => Z.1) (dgnExtendEq e ef el) =
  extendCong (T := νSetTel) (f_equal (fun Z: DgnPrefix n => Z.1) e)
    (eq_sym (rew_map (@νFillerType n) (fun Z: DgnPrefix n => Z.1) e a.1) • ef).
Proof.
  destruct e, a as [F L], b as [G M]; cbn in ef, el.
  destruct ef; cbn in el. destruct el. reflexivity.
Qed.

Definition dgnPackPath m (X: νDgnSets):
  (νDgnPack m X).1 = X.(approx) m leR_O := limitPackPath m X.

Lemma dgnPackPathS m (X: νDgnSets):
  f_equal (@dgnBond m) (dgnPackPath m.+1 X) • X.(approxS) m leR_O leR_O =
  dgnPackPath m X.
Proof.
  pose proof (limitPackPathS m X) as H.
  now rewrite eq_trans_refl_l in H.
Qed.

End νDgnSetEquiv.

Module νDgnSetEquivSimplicial := νDgnSetEquiv SimplicialLayer.
Module νDgnSetEquivCubical := νDgnSetEquiv CubicalLayer.
