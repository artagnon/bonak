(** Recovering an indexed degeneracy tower from its presheaf. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import Nat Tactics SigT HSet Limit Equiv.
Import Logic.EqNotations.

From Bonak.Presheaf Require Import Presentation.
From Bonak.νSet Require Import Layer.
From Bonak.Equiv.Dgn Require Import νDgnSetEquiv.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module νDgnSetRoundtrip (A: LayerSig).
Import A.
Module Export DgnEq := Bonak.Equiv.Dgn.νDgnSetEquiv.νDgnSetEquiv A.

Definition prefixFaceFuel {n} (P: (νSetAt n.+1).(prefix)) fuel (ε: arity)
  (d: νFrame P): νTotalType P :=
  νFace (dcStepIter fuel
    (n; (0; (prefixDepsCohs P; DepsCohsChainNil)))).2.2.2 ε d.

Lemma prefixFaceFuelRew {n} {P Q: (νSetAt n.+1).(prefix)} (e: P = Q)
  fuel (ε: arity) (d: νFrame Q):
  prefixFaceFuel P fuel ε (rew <- [νFrameDom] e in d) =
  rew <- [νTotalType] e in prefixFaceFuel Q fuel ε d.
Proof.
  now destruct e.
Qed.

Lemma prefixFaceFuelEq {n} (P: (νSetAt n.+1).(prefix)) (E: νFillerType P)
  fuel (ε: arity) (d: νFrame P):
  prefixFaceFuel P fuel ε d =
  faceDown (dgnDepsCohs2 (νDataAt P.1) P.2 E) fuel ε d.
Proof.
  unfold prefixFaceFuel, faceDown. rewrite chain2DownIter. reflexivity.
Qed.

Definition dgnStepInput n (Z: DgnStepBase n.+1): Type := νTotalType Z.1.1.

Lemma dgnStepBaseEqInput n {P Q: DgnPrefix n.+1} (e: P = Q)
  {F: νFillerType P.1} {G: νFillerType Q.1}
  (ef: rew [fun Z: DgnPrefix n.+1 => νFillerType Z.1] e in F = G)
  (x: νTotalType Q.1):
  rew <- [dgnStepInput n]
    (eq_existT_curried e ef: ((P; F): DgnStepBase n.+1) = (Q; G)) in
    (x: dgnStepInput n (Q; G)) =
  rew <- [@νTotalType n] (f_equal (fun Z: DgnPrefix n.+1 => Z.1) e) in x.
Proof.
  destruct e. cbn in ef. destruct ef. reflexivity.
Qed.

Definition dgnStepPrefix n (Z: DgnStepBase n): (νSetAt n.+1).(prefix) :=
  (Z.1.1; Z.2).

Lemma dgnStepPrefixEq {n} {P Q: DgnPrefix n} (e: P = Q)
  {F: νFillerType P.1} {G: νFillerType Q.1}
  (ef: rew [fun Z: DgnPrefix n => νFillerType Z.1] e in F = G):
  f_equal (dgnStepPrefix n)
    (eq_existT_curried e ef: ((P; F): DgnStepBase n) = (Q; G)) =
  extendCong (T := νSetChain) (f_equal (fun Z: DgnPrefix n => Z.1) e)
    (eq_sym (rew_map (@νFillerType n) (fun Z: DgnPrefix n => Z.1) e F) • ef).
Proof.
  destruct e. cbn in ef. destruct ef. reflexivity.
Qed.

Definition dgnStepOutput n (Z: DgnStepBase n.+1): Type :=
  {D: νFrame Z.1.1 &T Z.2 D}.

Definition dgnLayerMap n (Z: DgnStepBase n.+1) (L: dgnLayerType n.+1 Z)
  i (Hi: i <= n) (x: dgnStepInput n Z): dgnStepOutput n Z :=
  (mkReflFrameAbove
    (dgnDepsReflCohsSupFromData (νDataAt Z.1.1.1) Z.1.1.2 Z.2
      ((νDgnSetAt n).(dgnStepData) Z.1.1.1 Z.1.2.1 Z.1.1.2 Z.1.2.2))
    (n - i) (sub_leR n i) x.1 x.2;
   L.1 (n - i) (sub_leR n i) x.1 x.2).

Lemma dgnLayerEqByMap n (Z: DgnStepBase n.+1) (L M: dgnLayerType n.+1 Z)
  (H: forall i (Hi: i <= n) x,
    dgnLayerMap n Z L i Hi x = dgnLayerMap n Z M i Hi x): L = M.
Proof.
  apply dgnLayerEq. intros i Hi d c.
  pose proof (H (n - i) (sub_leR n i) (d; c)) as h.
  unfold dgnLayerMap in h.
  revert h. generalize (sub_leR n (n - i)).
  rewrite (subSubCancel Hi). intros Hi' h.
  exact (totalSndEq (B := νFrame Z.1.1) (P := fun D => Z.2 D) eq_refl h).
Qed.

Lemma dgnLayerRewEq n {Z W: DgnStepBase n.+1} (e: Z = W)
  (L: dgnLayerType n.+1 Z) (M: dgnLayerType n.+1 W)
  (H: forall i (Hi: i <= n) (x: dgnStepInput n W),
    rew <- [dgnStepOutput n] e in dgnLayerMap n W M i Hi x =
    dgnLayerMap n Z L i Hi (rew <- [dgnStepInput n] e in x)):
  rew [dgnLayerType n.+1] e in L = M.
Proof.
  destruct e. apply dgnLayerEqByMap. intros i Hi x.
  symmetry. exact (H i Hi x).
Qed.

Section FG.
Variable X: νDgnSets.
Let psh := (g X).1.
Let dgn := (g X).2.

Definition pshFrameAt n: psh.(F0) n -> νFrame (pshApprox psh n) :=
  match n with
  | 0 => fun _ => tt
  | n.+1 => mkPshFrame psh (towerPshDeps psh (pshTw psh n))
  end.

Definition FgFrame n (e: pshApprox psh n = (νDgnPack n X).1.1): Type :=
  forall x: psh.(F0) n, pshFrameAt n x =
    rew <- [@νFrameDom n] e in (x.1: νFrameDom (νDgnPack n X).1.1).

Definition fgFillers n (e: pshApprox psh n = (νDgnPack n X).1.1)
  (H: FgFrame n e):
  νFillerEqvType e (this (pshFrom psh n)) (this (νDgnPack n X).2).1.
Proof.
  destruct n.
  - exact (fun D => fillerEquivOf (rewEquiv νFrameDom (eq_sym e))
      eq_refl (pshFrameAt 0) (fun D c => H (D; c)) D).
  - exact (fun D => fillerEquivOf (rewEquiv νFrameDom (eq_sym e))
      eq_refl (pshFrameAt n.+1) (fun D c => H (D; c)) D).
Defined.

Lemma fgFillersTotal n (e: pshApprox psh n = (νDgnPack n X).1.1)
  (H: FgFrame n e) (x: psh.(F0) n):
  rew <- [@νTotalType n]
    (extendCong (T := νSetChain) e (νFillerEq e (fgFillers n e H)))
    in (x: νTotalType (νDgnPack n.+1 X).1.1) =
  invEq (pshTotalEquiv psh n) x.
Proof.
  rewrite rewTotalνFillerEq.
  symmetry. destruct n.
  - exact (fillerEquivOfWhole (rewEquiv νFrameDom (eq_sym e)) eq_refl
      (pshFrameAt 0) (fun D c => H (D; c)) x.1 x.2).
  - exact (fillerEquivOfWhole (rewEquiv νFrameDom (eq_sym e)) eq_refl
      (pshFrameAt n.+1) (fun D c => H (D; c)) x.1 x.2).
Qed.

Definition fgUnderlying n
  (e: pshDgnApprox psh dgn n = (νDgnPack n X).1):
  pshApprox psh n = (νDgnPack n X).1.1 :=
  f_equal (fun Z: DgnPrefix n => Z.1) e.

Definition fgFillerPath n
  (e: pshDgnApprox psh dgn n = (νDgnPack n X).1)
  (H: FgFrame n (fgUnderlying n e)):
  rew [fun Z: DgnPrefix n => νFillerType Z.1] e in
    (this (pshFrom psh n): νFillerType (pshDgnApprox psh dgn n).1) =
  (this (νDgnPack n X).2).1 :=
  rew_map (@νFillerType n) (fun Z: DgnPrefix n => Z.1) e (this (pshFrom psh n)) •
  νFillerEq (fgUnderlying n e) (fgFillers n (fgUnderlying n e) H).

Definition fgStepPath n
  (e: pshDgnApprox psh dgn n = (νDgnPack n X).1)
  (H: FgFrame n (fgUnderlying n e)):
  ((pshDgnApprox psh dgn n; this (pshFrom psh n)): DgnStepBase n) =
  ((νDgnPack n X).1; (this (νDgnPack n X).2).1) :=
  eq_existT_curried e (fgFillerPath n e H).

Lemma fgStepOutput n
  (e: pshDgnApprox psh dgn n.+1 = (νDgnPack n.+1 X).1)
  (H: FgFrame n.+1 (fgUnderlying n.+1 e)) (x: psh.(F0) n.+1):
  rew <- [dgnStepOutput n] (fgStepPath n.+1 e H) in
    (x: dgnStepOutput n ((νDgnPack n.+1 X).1; (this (νDgnPack n.+1 X).2).1)) =
  invEq (pshTotalEquiv psh n.+1) x.
Proof.
  change (rew <- [fun Z: DgnStepBase n.+1 => νTotalType (dgnStepPrefix n.+1 Z)]
    (fgStepPath n.+1 e H) in
    (x: νTotalType (dgnStepPrefix n.+1
      ((νDgnPack n.+1 X).1; (this (νDgnPack n.+1 X).2).1))) =
    invEq (pshTotalEquiv psh n.+1) x).
  unfold eq_rect_r. rewrite rew_map, <- eq_sym_map_distr.
  unfold fgStepPath. rewrite dgnStepPrefixEq.
  unfold fgFillerPath. rewrite eq_trans_sym_cancel_l.
  apply fgFillersTotal.
Qed.

Lemma fgStepInput n
  (e: pshDgnApprox psh dgn n.+1 = (νDgnPack n.+1 X).1)
  (H: FgFrame n.+1 (fgUnderlying n.+1 e)) (x: psh.(F0) n):
  rew <- [dgnStepInput n] (fgStepPath n.+1 e H) in
    (x: dgnStepInput n ((νDgnPack n.+1 X).1; (this (νDgnPack n.+1 X).2).1)) =
  rew <- [@νTotalType n] (fgUnderlying n.+1 e) in
    (x: νTotalType (νDgnPack n.+1 X).1.1).
Proof.
  apply dgnStepBaseEqInput.
Qed.

Lemma fgFrameStep n
  (e: pshApprox psh n.+1 = (νDgnPack n.+1 X).1.1)
  (H: forall x: psh.(F0) n,
    rew <- [@νTotalType n] e in (x: νTotalType (νDgnPack n.+1 X).1.1) =
    invEq (pshTotalEquiv psh n) x)
  (x: psh.(F0) n.+1):
  mkPshFrame psh (towerPshDeps psh (pshTw psh n)) x =
  rew <- [@νFrameDom n.+1] e in (x.1: νFrameDom (νDgnPack n.+1 X).1.1).
Proof.
  apply (faceDownEq (νDepsCohs2At (pshFrom psh n))). intros q Hq ε.
  rewrite <- !(prefixFaceFuelEq (pshApprox psh n.+1) (this (pshFrom psh n.+1))),
    prefixFaceFuelRew.
  rewrite H. apply (pshCellInj psh n).
  rewrite (prefixFaceFuelEq (pshApprox psh n.+1) (this (pshFrom psh n.+1))).
  match goal with |- _ = ?rhs =>
    change (pshCell psh n (faceDown (νDepsCohs2At (pshFrom psh n)) q ε
      (invEq (pshTotalEquiv psh n.+1) x).1) = rhs)
  end.
  rewrite (pshCellFaceDown psh n q Hq).
  unfold pshCell. rewrite !secEq.
  unfold pshRevFace.
  change (faceDown (dgnPositionCohs2 n (νDgnPack n X)) (n - (n - q)) ε x.1 =
    prefixFaceFuel (νDgnPack n.+1 X).1.1 q ε x.1).
  rewrite (subSubCancel Hq).
  symmetry.
  exact (prefixFaceFuelEq (νDgnPack n.+1 X).1.1
    (this (νDgnPack n.+1 X).2).1 q ε x.1).
Qed.

Definition FgTotal n (u: pshApprox psh n.+1 = (νDgnPack n.+1 X).1.1): Type :=
  forall x: psh.(F0) n,
    rew <- [@νTotalType n] u in (x: νTotalType (νDgnPack n.+1 X).1.1) =
    invEq (pshTotalEquiv psh n) x.

Lemma fgLayer n
  (e: pshDgnApprox psh dgn n.+1 = (νDgnPack n.+1 X).1)
  (HT: FgTotal n (fgUnderlying n.+1 e))
  (HF: FgFrame n.+1 (fgUnderlying n.+1 e)):
  rew [dgnLayerType n.+1] (fgStepPath n.+1 e HF) in
    ((this (pshDgnFrom psh dgn n.+1)).2:
      dgnLayerType n.+1 (pshDgnApprox psh dgn n.+1; this (pshFrom psh n.+1))) =
  (this (νDgnPack n.+1 X).2).2.
Proof.
  apply dgnLayerRewEq. intros i Hi x.
  rewrite fgStepOutput, fgStepInput, HT.
  apply (pshCellInj psh n.+1).
  change (pshTotalEquiv psh n.+1
    (invEq (pshTotalEquiv psh n.+1) (dgn.(Dgn _) n i Hi x)) =
    pshRevDgn psh dgn n (n - i) (sub_leR n i)
      (pshCell psh n (invEq (pshTotalEquiv psh n) x))).
  unfold pshCell, pshRevDgn. rewrite !secEq.
  generalize (sub_leR n (n - i)).
  rewrite (subSubCancel Hi). intro H. reflexivity.
Qed.

(** The level step, given the frame identification at the level and a
    layer path over the resulting filler path: the datum path, and the
    identification of the total spaces one level up along the underlying
    νSet prefix path. *)

Definition fgStepAt n (e: pshDgnApprox psh dgn n = (νDgnPack n X).1)
  (HF: FgFrame n (fgUnderlying n e))
  (L: dgnLayerType n (pshDgnApprox psh dgn n; this (pshFrom psh n)))
  (el: rew [dgnLayerType n] (fgStepPath n e HF) in L =
    (this (νDgnPack n X).2).2):
  { h: rew [dgnIncrType] e in
         ((this (pshFrom psh n); L): dgnIncrType (pshDgnApprox psh dgn n))
       = this (νDgnPack n X).2 &T
    FgTotal n (f_equal (fun Z: DgnPrefix n.+1 => Z.1)
      (extendCong (T := dgnChain) e h)) }.
Proof.
  exists (dgnIncrEq e (a := (this (pshFrom psh n); L))
    (b := this (νDgnPack n X).2) (fgFillerPath n e HF) el).
  intro x. rewrite dgnIncrEqUnderlying.
  unfold fgFillerPath. rewrite eq_trans_sym_cancel_l.
  now apply fgFillersTotal.
Defined.

(** The chain of prefix paths

    The paths are produced level by level by [limitEqOfPositions], over
    the presheaf positions [pshDgnPosition]. Since [pshDgnApprox] is defined
    by cases on the level, the one-step unfolding of a position is the next
    one by a path defined by cases ([pshDgnPositionNext]), and the step
    proceeds by cases too. Above level [0], the state is the identification
    of the total spaces carried along the prefix path, from which
    [fgFrameStep] derives the frame identification of the level. *)

Definition FgState n: pshDgnApprox psh dgn n = (νDgnPack n X).1 -> Type :=
  match n with
  | 0 => fun _ => unit
  | n.+1 => fun e => FgTotal n (fgUnderlying n.+1 e)
  end.

Definition fgPositionNext n:
  pshDgnPosition psh dgn n.+1 = dgnPositionNext n (pshDgnPosition psh dgn n) :=
  eq_sym (pshDgnPositionNext psh dgn n).

Definition fgStep n (e: pshDgnApprox psh dgn n = (νDgnPack n X).1)
  (s: FgState n e):
  { h: rew [dgnIncrType] e in this (pshDgnFrom psh dgn n)
       = this (νDgnPack n X).2 &T
    FgState n.+1
      (rew <- [fun P: DgnPosition n.+1 => P.1 = (νDgnPack n.+1 X).1]
         fgPositionNext n in
       (extendCong (T := dgnChain) e h:
         (dgnPositionNext n (pshDgnPosition psh dgn n)).1 = _)) }.
Proof.
  destruct n as [|n].
  - now exact (fgStepAt 0 e (fun _ => hunit_ext tt _) _ (hunit_ext _ _)).
  - now exact (fgStepAt n.+1 e (fgFrameStep n (fgUnderlying n.+1 e) s) _
      (fgLayer n e s _)).
Defined.

Definition fg: f psh dgn = X :=
  limitEqOfPositions (T := dgnChain) (pshDgnPosition psh dgn)
    fgPositionNext X FgState tt fgStep.

End FG.
End νDgnSetRoundtrip.

Module νDgnSetRoundtripSimplicial := νDgnSetRoundtrip SimplicialLayer.
Module νDgnSetRoundtripCubical := νDgnSetRoundtrip CubicalLayer.
