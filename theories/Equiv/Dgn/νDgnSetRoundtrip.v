(** Recovering an indexed degeneracy tower from its presheaf. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet LeSProp NatLemmas Notation RewLemmas
  νSet.Layer Equiv.Dgn.νDgnSetEquiv Limit.
From Bonak.Lib Require Import Equiv.

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
  extendCong (T := νSetTel) (f_equal (fun Z: DgnPrefix n => Z.1) e)
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
    (extendCong (T := νSetTel) e (νFillerEq e (fgFillers n e H)))
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

Definition FgTotal n
  (e: pshDgnApprox psh dgn n.+1 = (νDgnPack n.+1 X).1): Type :=
  forall x: psh.(F0) n,
    rew <- [@νTotalType n] (fgUnderlying n.+1 e) in
      (x: νTotalType (νDgnPack n.+1 X).1.1) =
    invEq (pshTotalEquiv psh n) x.

Lemma fgLayer n
  (e: pshDgnApprox psh dgn n.+1 = (νDgnPack n.+1 X).1)
  (HT: FgTotal n e) (HF: FgFrame n.+1 (fgUnderlying n.+1 e)):
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

Definition fgNext n
  (e: pshDgnApprox psh dgn n.+1 = (νDgnPack n.+1 X).1)
  (HT: FgTotal n e):
  pshDgnApprox psh dgn n.+2 = (νDgnPack n.+2 X).1 :=
  let HF := fgFrameStep n (fgUnderlying n.+1 e) HT in
  dgnExtendEq e (a := this (pshDgnFrom psh dgn n.+1))
    (b := this (νDgnPack n.+1 X).2)
    (fgFillerPath n.+1 e HF) (fgLayer n e HT HF).

Lemma fgNextTotal n
  (e: pshDgnApprox psh dgn n.+1 = (νDgnPack n.+1 X).1)
  (HT: FgTotal n e): FgTotal n.+1 (fgNext n e HT).
Proof.
  unfold FgTotal, fgUnderlying, fgNext. intro x.
  rewrite (dgnExtendEqUnderlying e
    (a := this (pshDgnFrom psh dgn n.+1)) (b := this (νDgnPack n.+1 X).2)
    (fgFillerPath n.+1 e (fgFrameStep n (fgUnderlying n.+1 e) HT))
    (fgLayer n e HT (fgFrameStep n (fgUnderlying n.+1 e) HT))).
  unfold fgFillerPath. rewrite eq_trans_sym_cancel_l.
  apply fgFillersTotal.
Qed.

Lemma fgNextBond n
  (e: pshDgnApprox psh dgn n.+1 = (νDgnPack n.+1 X).1)
  (HT: FgTotal n e):
  f_equal (@dgnBond n.+1) (fgNext n e HT) = e.
Proof.
  exact (dgnExtendEqBond e
    (a := this (pshDgnFrom psh dgn n.+1)) (b := this (νDgnPack n.+1 X).2)
    (fgFillerPath n.+1 e (fgFrameStep n (fgUnderlying n.+1 e) HT))
    (fgLayer n e HT (fgFrameStep n (fgUnderlying n.+1 e) HT))).
Qed.

Definition fgFrame0: FgFrame 0 eq_refl := fun x => hunit_ext tt x.1.

Definition fgBase: pshDgnApprox psh dgn 1 = (νDgnPack 1 X).1 :=
  dgnExtendEq eq_refl (a := this (pshDgnFrom psh dgn 0)) (b := this X)
    (fgFillerPath 0 eq_refl fgFrame0) (hunit_ext _ _).

Lemma fgBaseTotal: FgTotal 0 fgBase.
Proof.
  unfold FgTotal, fgUnderlying, fgBase. intro x.
  rewrite (dgnExtendEqUnderlying eq_refl
    (a := this (pshDgnFrom psh dgn 0)) (b := this X)
    (fgFillerPath 0 eq_refl fgFrame0) (hunit_ext _ _)).
  unfold fgFillerPath. rewrite eq_trans_sym_cancel_l.
  apply fgFillersTotal.
Qed.

Fixpoint fgChain n:
  {e: pshDgnApprox psh dgn n.+1 = (νDgnPack n.+1 X).1 &T FgTotal n e} :=
  match n with
  | 0 => (fgBase; fgBaseTotal)
  | n.+1 =>
      let s := fgChain n in
      (fgNext n s.1 s.2; fgNextTotal n s.1 s.2)
  end.

Definition fgPrefix n: pshDgnApprox psh dgn n = (νDgnPack n X).1 :=
  match n with
  | 0 => eq_refl
  | n.+1 => (fgChain n).1
  end.

Definition pshDgnBond n:
  @dgnBond n (pshDgnApprox psh dgn n.+1) = pshDgnApprox psh dgn n :=
  match n with 0 => eq_refl | n.+1 => eq_refl end.

Lemma fgPrefixBond n:
  f_equal (@dgnBond n) (fgPrefix n.+1) = pshDgnBond n • fgPrefix n.
Proof.
  destruct n.
  - exact (dgnExtendEqBond eq_refl
      (a := this (pshDgnFrom psh dgn 0)) (b := this X)
      (fgFillerPath 0 eq_refl fgFrame0) (hunit_ext _ _)).
  - cbn [fgPrefix fgChain pshDgnBond].
    rewrite eq_trans_refl_l. apply fgNextBond.
Qed.

Theorem fg: f psh dgn = X.
Proof.
  unshelve eapply limitEqIntro.
  - exact (fun n => fgPrefix n • dgnPackPath n X).
  - apply ({_: hunit & hunit}).(UIP).
  - intro n. cbv beta.
    rewrite eq_trans_map_distr, <- eq_trans_assoc.
    rewrite (dgnPackPathS n X), (fgPrefixBond n).
    rewrite eq_trans_assoc. reflexivity.
Qed.

End FG.
End νDgnSetRoundtrip.

Module νDgnSetRoundtripSimplicial := νDgnSetRoundtrip SimplicialLayer.
Module νDgnSetRoundtripCubical := νDgnSetRoundtrip CubicalLayer.
