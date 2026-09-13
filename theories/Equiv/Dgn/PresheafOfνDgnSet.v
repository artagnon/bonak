(** Cells, faces, and degeneracy maps read from the combined tower. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet LeSProp NatLemmas Notation νSet.Layer
  νDgnSet Equiv.PresheafOfνSet Equiv.PresheafRoundtrip Equiv.Dgn.PresheafEquiv Limit.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module PresheafOfνDgnSet (A: LayerSig).
Import A.

Module Export DgnSet := νDgnSet.νDgnSet A.
Module Export SetRoundtrip := Bonak.Equiv.PresheafRoundtrip.PresheafRoundtripOn A DgnSet.νSet.
Module PshOfSet := SetRoundtrip.νSetRoundtrip.PresheafOfνSet.
Module Export PshEquiv := Bonak.Equiv.Dgn.PresheafEquiv.PresheafEquivOn A
  PshOfSet.νSetOfPresheaf.PshEq.

Definition DgnPosition n: Type := {Y: DgnPrefix n &T νDgnSetsFrom n Y}.

Definition dgnPositionNext n (s: DgnPosition n): DgnPosition n.+1 :=
  (dgnExtend s.1 (this s.2); next s.2).

Definition dgnPositionTotal n (s: DgnPosition n): HSet :=
  {D: νFrame s.1.1 & (this s.2).1 D}.

Definition dgnPositionCohs2 n (s: DgnPosition n): DepsCohs2 n 0 :=
  dgnDepsCohs2 (νDataAt s.1.1) (this s.2).1 (this (next s.2)).1.

Definition dgnPositionDeps n (s: DgnPosition n): DepsReflCohsSup n 0 :=
  dgnDepsReflCohsSupFromData (νDataAt s.1.1)
    (this s.2).1 (this (next s.2)).1
    ((νDgnSetAt n).(dgnStepData) s.1.1 s.1.2 (this s.2).1 (this s.2).2).

Definition dgnPositionMap n (s: DgnPosition n) i (Hi: i <= n)
  (x: dgnPositionTotal n s): dgnPositionTotal n.+1 (dgnPositionNext n s) :=
  (mkReflFrameAbove (dgnPositionDeps n s) (n - i) (sub_leR n i) x.1 x.2;
   (this (next s.2)).2.1 (n - i) (sub_leR n i) x.1 x.2).

Definition νDgnPack (m: nat) (X: νDgnSets): DgnPosition m := limitPack m X.

(** Unfolding the tower gives prefixes whose bonding equations reduce to
    reflexivity. The underlying νSet tower therefore has the same fillers
    by conversion, including after taking [next]. *)

Definition underlyingFrom (X: νDgnSets) (m: nat):
  νSetFrom m (νDgnPack m X).1.1 :=
  ofChain (T := νSetTel) (fun l => (νDgnPack l X).1.1)
    (fun _ => eq_refl) m.

Definition dgnF0 (X: νDgnSets) (n: nat): HSet :=
  νTotal (underlyingFrom X n).

Definition dgnFace (X: νDgnSets) n i (Hi: i <= n) (ε: arity):
  dgnF0 X n.+1 -> dgnF0 X n :=
  νFaceFuel (underlyingFrom X n) (n - i) ε.

Definition underlyingPresheaf (X: νDgnSets): PshEq.Psh.Presheaf := {|
  F0 := dgnF0 X;
  Face := dgnFace X;
  FaceCoh := fun n q Hq r Hr ε ω d =>
    νFaceFuelCoh (underlyingFrom X n) q Hq r Hr ε ω d;
|}.

Definition dgnDataAt (X: νDgnSets) n:
  DgnData (νDataAt (νDgnPack n X).1.1) (this (νDgnPack n X).2).1 :=
  (νDgnSetAt n).(dgnStepData) (νDgnPack n X).1.1
    (νDgnPack n X).1.2 (this (νDgnPack n X).2).1
    (this (νDgnPack n X).2).2.

Definition faceDown {p k} (dc2: DepsCohs2 p k) (fuel: nat) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := dc2.(_depsCohs)))) :=
  νFace (dc2PackDeps (chain2Down dc2 fuel)).2.2.2 ε d.

Definition dgnPositionFace n (s: DgnPosition n) i (Hi: i <= n) (ε: arity)
  (x: dgnPositionTotal n.+1 (dgnPositionNext n s)): dgnPositionTotal n s :=
  faceDown (dgnPositionCohs2 n s) (n - i) ε x.1.

Lemma faceDownStep {p k} (dc2: DepsCohs2 p.+1 k) fuel (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := dc2.(_depsCohs)))):
  faceDown dc2 fuel.+1 ε d =
  let y := faceDown (proj1DepsCohs2 dc2) fuel ε d.1 in
  ((y.1; y.2.1); y.2.2).
Proof.
  unfold faceDown.
  replace fuel.+1 with (fuel + 1) by
    now rewrite <- plus_n_Sm, <- plus_n_O.
  rewrite (chain2DownCat dc2 1 fuel).
  unfold chain2Cat, dc2PackDeps.
  cbn [projT1 projT2].
  rewrite cohs2ChainDepsCohsCompose, νFaceCompose.
  reflexivity.
Qed.

Lemma faceDownEq {p k} (dc2: DepsCohs2 p k)
  (d d': mkFrame (mkDepsRestr (depsCohs := dc2.(_depsCohs))))
  (H: forall i, i <= p -> forall ε,
    faceDown dc2 i ε d = faceDown dc2 i ε d'): d = d'.
Proof.
  revert k dc2 d d' H; induction p; intros k dc2 d d' H.
  all: apply (frameEqStep DepsCohsChainNil d d' (H 0 leR_O)).
  - exact (hunit_ext _ _).
  - apply (IHp _ (proj1DepsCohs2 dc2)). intros i Hi ε.
    pose proof (H i.+1 (⇑ Hi) ε) as e.
    rewrite 2 faceDownStep in e.
    exact (getPaintingEq (ExtChainCons ExtChainNil) _ _ _ _ e).
Qed.

Definition dgnDepsAt (X: νDgnSets) n: DepsReflCohsSup n 0 :=
  dgnDepsReflCohsSupFromData _ _ (this (νDgnPack n.+1 X).2).1 (dgnDataAt X n).

Definition dgnDeps2At (X: νDgnSets) n: DepsReflCohs2 n 0 :=
  dgnDepsReflCohs2FromData _ _ _ (this (νDgnPack n.+2 X).2).1
    (dgnDataAt X n) (this (νDgnPack n.+1 X).2).2.1
    (this (νDgnPack n.+1 X).2).2.2.

Lemma faceDownAboveId {p k} (deps: DepsReflCohsSup p k)
  i (Hi: i <= p) (ε: arity)
  (d: mkFrame (RestrOfReflCohsSup deps))
  (c: mkPainting (RestrExtOfReflCohsSup deps) d):
  faceDown (Cohs2OfReflCohsSup deps) i ε (mkReflFrameAbove deps i Hi d c) =
  (d; c).
Proof.
  revert p k deps Hi d c; induction i; intros p k deps Hi d c.
  - unfold faceDown, mkReflFrameAbove, mkReflFramesAbove,
      mkReflFramesAboveOf0AndS, mkReflFrameAboveOf0AndS.
    cbn [projT2].
    unfold mkReflFrameAbove0, mkReflLayerAbove0.
    cbn [chain2Down dc2PackDeps νFace cohsChainExt cohsChainNext
      getFrame getPainting projT1 projT2].
    rewrite nth_lam.
    symmetry.
    exact (eq_existT_curried
      (mkIdRestrReflFrameBelow deps.(_depsReflCohsInf) 0 leR_O ε d) eq_refl).
  - destruct p; [now destruct (leR_O_contra Hi) |].
    rewrite faceDownStep.
    change
      ((let y := faceDown (Cohs2OfReflCohsSup deps.(1)%depsreflcohssup) i ε
          (mkReflFrameAbove deps.(1)%depsreflcohssup i Hi d.1 (d.2; c)) in
        (((y.1; y.2.1); y.2.2):
          {d': mkFrame (RestrOfReflCohsSup deps) &T
            mkPainting (RestrExtOfReflCohsSup deps) d'})) = (d; c)).
    now rewrite IHi.
Qed.

Definition aboveTotal {p k} (deps: DepsReflCohsSup p k)
  (extra: DepsReflCohsSupExtension p k deps) i (Hi: i <= p)
  (d: mkFrame (RestrOfReflCohsSup deps))
  (c: mkPainting (RestrExtOfReflCohsSup deps) d):
  {d': mkFrame (mkDepsRestr (depsCohs := CohsOfReflCohsSup deps)) &T
    mkPainting (mkExtraDeps (CohsExtOfReflCohsSup deps)) d'} :=
  (mkReflFrameAbove deps i Hi d c; mkReflPaintingAbove deps extra i Hi d c).

Lemma aboveTotalStep {p k} (deps: DepsReflCohsSup p.+1 k)
  (extra: DepsReflCohsSupExtension p.+1 k deps) i (Hi: i <= p)
  (d: mkFrame (RestrOfReflCohsSup deps))
  (c: mkPainting (RestrExtOfReflCohsSup deps) d):
  aboveTotal deps extra i.+1 (⇑ Hi) d c =
  let y := aboveTotal deps.(1)%depsreflcohssup (AddReflCohSupDep deps extra)
    i Hi d.1 (d.2; c) in
  ((y.1; y.2.1); y.2.2).
Proof.
  reflexivity.
Qed.

Lemma faceDownAboveSup {p k} (deps: DepsReflCohs2 p k)
  q i (Hq: q <= i) (Hi: i <= p) (ε: arity)
  (d: mkFrame (RestrOfReflCohsSup (mkDepsReflCohsSup deps)))
  (c: mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps)) d):
  faceDown (Cohs2OfReflCohsSup (mkDepsReflCohsSup deps)) q ε
    (mkReflFrameAbove (mkDepsReflCohsSup deps) i.+1 (⇑ Hi) d c) =
  let y := faceDown (Cohs2OfReflCohsSup deps.(_depsReflCohsSup)) q ε d in
  aboveTotal deps.(_depsReflCohsSup) deps.(_extraDepsReflCohsSup) i Hi y.1 y.2.
Proof.
  revert p k deps i Hq Hi d c; induction q; intros p k deps i Hq Hi d c.
  - unfold faceDown, aboveTotal.
    cbn [chain2Down dc2PackDeps νFace cohsChainExt cohsChainNext
      getFrame getPainting projT1 projT2].
    unfold mkReflFrameAbove, mkReflFramesAbove, mkReflFramesAboveOf0AndS,
      mkReflFrameAboveOf0AndS.
    cbn [projT2].
    unfold mkReflFramesAboveS.
    cbn [mkCohReflRestrFrameAboveSupTypesAndReflFramesAbove
      ReflFramesAboveSDef mkReflLayerAbove projT1 projT2].
    rewrite nth_lam.
    symmetry.
    exact (eq_existT_curried
      ((mkCohReflRestrFramesAboveSup deps).2 i 0 Hi leR_O ε d.1 (d.2; c))
      eq_refl).
  - destruct i; [now destruct (leR_O_contra Hq) |].
    destruct p; [now destruct (leR_O_contra Hi) |].
    rewrite 2 faceDownStep.
    cbv zeta.
    rewrite (aboveTotalStep deps.(_depsReflCohsSup)
      deps.(_extraDepsReflCohsSup) i (⇓ Hi)).
    exact (f_equal
      (fun y:
        {d': mkFrame (RestrOfReflCohsSup (mkDepsReflCohsSup deps.(1)%depsreflcohs2)) &T
          mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps.(1)%depsreflcohs2)) d'} =>
        (((y.1; y.2.1); y.2.2):
          {d': mkFrame (RestrOfReflCohsSup (mkDepsReflCohsSup deps)) &T
            mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps)) d'}))
      (IHq _ _ deps.(1)%depsreflcohs2 i Hq Hi d.1 (d.2; c))).
Qed.

Definition belowPair {p k} (deps: DepsReflCohsSup p k)
  (extra: DepsReflCohsSupExtension p k deps) i (Hi: i <= k)
  (d: mkFrame (RestrOfReflCohsSup deps))
  (c: mkPainting (RestrExtOfReflCohsSup deps) d):
  {d': mkFrame (mkDepsRestr (depsCohs := CohsOfReflCohsSup deps)).(1) &T
    mkPainting (AddRestrDep _ (mkExtraDeps (CohsExtOfReflCohsSup deps))) d'} :=
  (mkReflFrameBelow deps.(_depsReflCohsInf) i Hi d;
   mkReflPaintingBelow deps extra i Hi d c).

Lemma belowPairStep {p k} (deps: DepsReflCohsSup p.+1 k)
  (extra: DepsReflCohsSupExtension p.+1 k deps) i (Hi: i <= k)
  (d: mkFrame (RestrOfReflCohsSup deps))
  (c: mkPainting (RestrExtOfReflCohsSup deps) d):
  belowPair deps extra i Hi d c =
  let y := belowPair deps.(1)%depsreflcohssup (AddReflCohSupDep deps extra)
    i.+1 (⇑ Hi) d.1 (d.2; c) in
  ((y.1; y.2.1); y.2.2).
Proof.
  reflexivity.
Qed.

Lemma faceDownBelowInf {p k} (deps: DepsReflCohs2 p k)
  q (Hq: q <= p) i (Hi: i <= k) (ε: arity)
  (d: mkFrame (RestrOfReflCohsSup (mkDepsReflCohsSup deps))):
  faceDown (Cohs2OfReflCohsSup (mkDepsReflCohsSup deps)).(1) q ε
    (mkReflFrameBelow (mkDepsReflCohsSup deps).(_depsReflCohsInf) i Hi d) =
  let y := faceDown (Cohs2OfReflCohsSup deps.(_depsReflCohsSup)) q ε d in
  belowPair deps.(_depsReflCohsSup) deps.(_extraDepsReflCohsSup) i Hi y.1 y.2.
Proof.
  revert p k deps Hq i Hi d; induction q; intros p k deps Hq i Hi d.
  - unfold faceDown, belowPair.
    cbn [chain2Down dc2PackDeps νFace cohsChainExt cohsChainNext
      getFrame getPainting projT1 projT2].
    unfold mkReflFrameBelow, mkReflFramesBelow.
    cbn [mkCohReflRestrFrameBelowInfTypesAndReflFramesBelow
      ReflFramesBelowDef mkReflLayerBelow projT1 projT2].
    rewrite nth_lmap.
    symmetry.
    exact (eq_existT_curried
      ((mkCohReflRestrFramesBelowInf deps).2 i 0 Hi leR_O ε d.1)
      eq_refl).
  - destruct p; [now destruct (leR_O_contra Hq) |].
    rewrite 2 faceDownStep. cbv zeta.
    rewrite (belowPairStep deps.(_depsReflCohsSup)
      deps.(_extraDepsReflCohsSup) i Hi).
    exact (f_equal
      (fun y:
        {d': mkFrame (mkDepsRestr (depsCohs :=
          CohsOfReflCohsSup deps.(_depsReflCohsSup).(1)%depsreflcohssup)).(1) &T
          mkPainting (AddRestrDep _ (mkExtraDeps (CohsExtOfReflCohsSup
            deps.(_depsReflCohsSup).(1)%depsreflcohssup))) d'} =>
        (((y.1; y.2.1); y.2.2):
          {d': mkFrame (mkDepsRestr (depsCohs :=
            CohsOfReflCohsSup deps.(_depsReflCohsSup))).(1) &T
            mkPainting (AddRestrDep _ (mkExtraDeps (CohsExtOfReflCohsSup
              deps.(_depsReflCohsSup)))) d'}))
      (IHq _ _ deps.(1)%depsreflcohs2 Hq i.+1 (⇑ Hi) d.1)).
Qed.

Lemma faceDownAboveInf {p k} (deps: DepsReflCohs2 p k)
  q i (Hi: i <= q) (Hq: q <= p) (ε: arity)
  (d: mkFrame (RestrOfReflCohsSup (mkDepsReflCohsSup deps)))
  (c: mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps)) d):
  faceDown (Cohs2OfReflCohsSup (mkDepsReflCohsSup deps)) q.+1 ε
    (mkReflFrameAbove (mkDepsReflCohsSup deps) i (Hi ↕ (↑ Hq)) d c) =
  let y := faceDown (Cohs2OfReflCohsSup deps.(_depsReflCohsSup)) q ε d in
  aboveTotal deps.(_depsReflCohsSup) deps.(_extraDepsReflCohsSup)
    i (Hi ↕ Hq) y.1 y.2.
Proof.
  revert p k deps q Hi Hq d c; induction i; intros p k deps q Hi Hq d c.
  - rewrite faceDownStep.
    exact (f_equal
      (fun y:
        {d': mkFrame (mkDepsRestr (depsCohs :=
          CohsOfReflCohsSup deps.(_depsReflCohsSup))).(1) &T
          mkPainting (AddRestrDep _ (mkExtraDeps (CohsExtOfReflCohsSup
            deps.(_depsReflCohsSup)))) d'} =>
        (((y.1; y.2.1); y.2.2):
          {d': mkFrame (RestrOfReflCohsSup (mkDepsReflCohsSup deps)) &T
            mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps)) d'}))
      (faceDownBelowInf deps q Hq 0 leR_O ε d)).
  - destruct q; [now destruct (leR_O_contra Hi) |].
    destruct p; [now destruct (leR_O_contra Hq) |].
    rewrite faceDownStep.
    rewrite (faceDownStep (Cohs2OfReflCohsSup deps.(_depsReflCohsSup)) q ε d).
    cbv zeta.
    rewrite (aboveTotalStep deps.(_depsReflCohsSup)
      deps.(_extraDepsReflCohsSup) i (Hi ↕ Hq)).
    exact (f_equal
      (fun y:
        {d': mkFrame (RestrOfReflCohsSup (mkDepsReflCohsSup deps.(1)%depsreflcohs2)) &T
          mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps.(1)%depsreflcohs2)) d'} =>
        (((y.1; y.2.1); y.2.2):
          {d': mkFrame (RestrOfReflCohsSup (mkDepsReflCohsSup deps)) &T
            mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps)) d'}))
      (IHi _ _ deps.(1)%depsreflcohs2 q Hi Hq d.1 (d.2; c))).
Qed.

(** The Above operation counts down from the last dimension, so the
    presheaf index [i] corresponds to [n - i]. *)

Definition dgnAbove (X: νDgnSets) n i (Hi: i <= n)
  (x: dgnF0 X n): dgnF0 X n.+1 :=
  (mkReflFrameAbove (dgnDepsAt X n) i Hi x.1 x.2;
   (this (νDgnPack n.+1 X).2).2.1 i Hi x.1 x.2).

Definition dgnMap (X: νDgnSets) n i (Hi: i <= n):
  dgnF0 X n -> dgnF0 X n.+1 :=
  dgnAbove X n (n - i) (sub_leR n i).

Lemma dgnFaceDgnId (X: νDgnSets) n i (Hi: i <= n) (ε: arity)
  (x: dgnF0 X n):
  dgnFace X n i Hi ε (dgnMap X n i Hi x) = x.
Proof.
  exact (faceDownAboveId (dgnDepsAt X n) (n - i) (sub_leR n i) ε x.1 x.2).
Qed.

Lemma dgnFaceDgnSup (X: νDgnSets) n i (Hi: i <= n) j (Hj: j <= i)
  (ε: arity) (x: dgnF0 X n.+1):
  dgnFace X n.+1 i.+1 (⇑ Hi) ε
    (dgnMap X n.+1 j (Hj ↕ (↑ Hi)) x) =
  dgnMap X n j (Hj ↕ Hi) (dgnFace X n i Hi ε x).
Proof.
  unfold dgnMap.
  generalize (sub_leR n.+1 j).
  rewrite (subSuccL (Hj ↕ Hi)). intro Hj'.
  exact (faceDownAboveSup (dgnDeps2At X n) (n - i) (n - j)
    (subAntitone Hj) (sub_leR n j) ε x.1 x.2).
Qed.

Lemma dgnFaceDgnInf (X: νDgnSets) n i j (Hij: i <= j) (Hj: j <= n)
  (ε: arity) (x: dgnF0 X n.+1):
  dgnFace X n.+1 i (Hij ↕ (↑ Hj)) ε
    (dgnMap X n.+1 j.+1 (⇑ Hj) x) =
  dgnMap X n j Hj (dgnFace X n i (Hij ↕ Hj) ε x).
Proof.
  unfold dgnFace, νFaceFuel.
  rewrite (subSuccL (Hij ↕ Hj)).
  exact (faceDownAboveInf (dgnDeps2At X n) (n - i) (n - j)
    (subAntitone Hij) (sub_leR n i) ε x.1 x.2).
Qed.

Lemma dgnAboveAbove (X: νDgnSets) n q r (Hq: q <= r) (Hr: r <= n)
  (x: dgnF0 X n):
  dgnAbove X n.+1 r.+1 (⇑ Hr) (dgnAbove X n q (Hq ↕ Hr) x) =
  dgnAbove X n.+1 q (Hq ↕ (↑ Hr)) (dgnAbove X n r Hr x).
Proof.
  apply (eq_existT_curried
    (((dgnDataAt X n.+1).(dgnDataCore).(cohReflAboveAboveFrames)
      (this (νDgnPack n.+2 X).2).1).2 q r Hq Hr x.1 x.2)).
  exact (((this (νDgnPack n.+2 X).2).2.2).2 q r Hq Hr x.1 x.2).
Qed.

Lemma dgnMapDgnMap (X: νDgnSets) n j i (Hji: j <= i) (Hi: i <= n)
  (x: dgnF0 X n):
  dgnMap X n.+1 j (Hji ↕ (↑ Hi)) (dgnMap X n i Hi x) =
  dgnMap X n.+1 i.+1 (⇑ Hi) (dgnMap X n j (Hji ↕ Hi) x).
Proof.
  unfold dgnMap.
  generalize (sub_leR n.+1 j).
  rewrite (subSuccL (Hji ↕ Hi)). intro Hj.
  exact (dgnAboveAbove X n (n - i) (n - j)
    (subAntitone Hji) (sub_leR n j) x).
Qed.

Definition gStructure (X: νDgnSets): PresheafDgn (underlyingPresheaf X) :=
  Build_PresheafDgn (underlyingPresheaf X) (dgnMap X)
    (dgnFaceDgnInf X) (dgnFaceDgnId X) (dgnFaceDgnSup X) (dgnMapDgnMap X).

Definition g (X: νDgnSets): Presheaf :=
  (underlyingPresheaf X; gStructure X).

End PresheafOfνDgnSet.

Module PresheafOfνDgnSetSimplicial := PresheafOfνDgnSet SimplicialLayer.
Module PresheafOfνDgnSetCubical := PresheafOfνDgnSet CubicalLayer.
