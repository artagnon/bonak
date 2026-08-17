(** The translation side of the backward round trip [f ∘ g] of the
    correspondence: [fg: νSetFromEquiv trTower0 (f (g X)) X].

    This file constructs the translation-equipped chains, filler
    equivalences, and level identifications used by the coinductive proof. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp NatLemmas Notation νSet.Layer
  νSet Face Presheaf νSetOfPresheaf PresheafOfνSet.
From Bonak.νSet.Lib Require Import Equiv.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module νSetRoundtrip (A: LayerSig).
Import A.

Module Export PresheafOfνSet := PresheafOfνSet.PresheafOfνSet A.

(** The face maps commute with the translations

    Chains of translation-equipped stages map to [DepsCohsChain]s on both
    sides. Along these chains, [getFrame] and [getPainting] compute on
    translated frames and paintings, and [νFace] commutes with the
    translations. This supplies the face equalities used by the [f ∘ g]
    frame identification. *)

Inductive TrCohsChain {P K} (TCTop: TrDepsCohs P K):
  forall {p k}, TrDepsCohs p k -> Type :=
| TrCohsChainNil: TrCohsChain TCTop TCTop
| TrCohsChainCons {p k} {TC: TrDepsCohs p.+1 k}:
    TrCohsChain TCTop TC -> TrCohsChain TCTop (proj1TrDepsCohs TC).

Arguments TrCohsChainNil {P K TCTop}.
Arguments TrCohsChainCons {P K TCTop p k TC} _.

Fixpoint trCohsChainA {P K} {TCTop: TrDepsCohs P K}
  {p k} {TC: TrDepsCohs p k} (C: TrCohsChain TCTop TC):
  DepsCohsChain (trDepsCohsA TCTop) (trDepsCohsA TC) :=
  match C with
  | TrCohsChainNil => DepsCohsChainNil
  | TrCohsChainCons C' => DepsCohsChainCons (trCohsChainA C')
  end.

Fixpoint trCohsChainB {P K} {TCTop: TrDepsCohs P K}
  {p k} {TC: TrDepsCohs p k} (C: TrCohsChain TCTop TC):
  DepsCohsChain (trDepsCohsB TCTop) (trDepsCohsB TC) :=
  match C with
  | TrCohsChainNil => DepsCohsChainNil
  | TrCohsChainCons C' => DepsCohsChainCons (trCohsChainB C')
  end.

Lemma trGetFrame {P K} {TCTop: TrDepsCohs P K}
  {p k} {TC: TrDepsCohs p k} (C: TrCohsChain TCTop TC)
  (d: mkFrame (mkDepsRestr (depsCohs := trDepsCohsB TCTop))):
  getFrame (cohsChainNext (trCohsChainA C))
    (mkFrameEqv (mkTrDepsRestr TCTop) d) =
  mkFrameEqv (mkTrDepsRestr TC)
    (getFrame (cohsChainNext (trCohsChainB C)) d).
Proof.
  induction C; cbn; [now reflexivity | now rewrite IHC].
Qed.

Lemma trGetPainting {P K} {TCTop: TrDepsCohs P K}
  {p k} {TC: TrDepsCohs p k} (C: TrCohsChain TCTop TC)
  (d: mkFrame TC.(_trDeps).(_depsB))
  (cp: mkPainting TC.(_tExtB) d):
  getPainting (cohsChainExt (trCohsChainA C))
    (mkFrameEqv TC.(_trDeps) d) (mkPaintingEqv TC.(_trExt) d cp) =
  (mkFrameEqv TCTop.(_trDeps)
     (getPainting (cohsChainExt (trCohsChainB C)) d cp).1;
   mkPaintingEqv TCTop.(_trExt)
     (getPainting (cohsChainExt (trCohsChainB C)) d cp).1
     (getPainting (cohsChainExt (trCohsChainB C)) d cp).2).
Proof.
  revert d cp; induction C; intros d cp.
  - now reflexivity.
  - now exact (IHC (d; cp.1) cp.2).
Qed.

(** [νFace] on a translated frame is the translated [νFace]: one
    cancellation of the diagonal translation coherence against the
    layer's transport, then the painting round trip. *)

Lemma νFaceTr {P K} {TCTop: TrDepsCohs P K}
  {p k} {TC: TrDepsCohs p k} (C: TrCohsChain TCTop TC) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := trDepsCohsB TCTop))):
  νFace (trCohsChainA C) ε (mkFrameEqv (mkTrDepsRestr TCTop) d) =
  (mkFrameEqv TCTop.(_trDeps) (νFace (trCohsChainB C) ε d).1;
   mkPaintingEqv TCTop.(_trExt) (νFace (trCohsChainB C) ε d).1
     (νFace (trCohsChainB C) ε d).2).
Proof.
  unfold νFace.
  rewrite trGetFrame.
  rewrite (trLayerEqvNth (mkPaintingEqvs TC.(_trExt))
    (mkTrRestrFrames TC) _ _ ε).
  refine (f_equal
    (fun z: {d0: mkFrame TC.(_trDeps).(_depsA) &T
       mkPainting TC.(_tExtA) d0} =>
     getPainting (cohsChainExt (trCohsChainA C)) z.1 z.2)
    (eq_existT_curried
      (eq_sym ((mkTrRestrFrames TC).2 0 leR_O ε
        (getFrame (cohsChainNext (trCohsChainB C)) d).1))
      (rew_sym_cancel _ _)) • _).
  now exact (trGetPainting C _ _).
Qed.

(** Lifting arbitrary chains to equipped chains

    [νFaceEq]'s hypothesis quantifies over *arbitrary* [DepsCohsChain]s
    from the shared top. Both equipped chain types — [PshCohsChain] on the
    presheaf side, [TrCohsChain] on the translation side — step by
    [proj1DepsCohs] on their [DepsCohs] images, so every chain is the
    image of an equipped one; the identification is carried as a
    sigma-package equality (the result type of [νFace] does not depend on
    the endpoint, so packages can be rewritten wholesale). *)

Lemma cohsChainStage {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc): p + cohsChainLen c = P.
Proof.
  induction c as [|p k dc c IH]; cbn [cohsChainLen].
  - now symmetry; apply plus_n_O.
  - rewrite <- plus_n_Sm. now exact IH.
Qed.

Lemma pshChainLift (psh: Presheaf) {M P K} (PCTop: PshDepsCohs psh M P K)
  {p k} {dc: DepsCohs p k}
  (c0: DepsCohsChain (pshDepsCohs psh PCTop) dc):
  {PC: PshDepsCohs psh M p k &T {C: PshCohsChain psh PCTop PC &T
    ((dc; c0): {dc0: DepsCohs p k &T
       DepsCohsChain (pshDepsCohs psh PCTop) dc0}) =
    (pshDepsCohs psh PC; pshCohsChainCohs psh C)}}.
Proof.
  induction c0 as [|p k dc' c0' IH].
  - now exact (PCTop; (PshCohsChainNil; eq_refl)).
  - destruct IH as (PC', (C', e')).
    refine (proj1PshDepsCohs psh PC'; (PshCohsChainCons C'; _)).
    now exact (f_equal (fun s: {dc0: DepsCohs p.+1 k &T
        DepsCohsChain (pshDepsCohs psh PCTop) dc0} =>
      ((proj1DepsCohs s.1; DepsCohsChainCons s.2):
        {dc0: DepsCohs p k.+1 &T
          DepsCohsChain (pshDepsCohs psh PCTop) dc0})) e').
Qed.

Lemma trChainLift {P K} (TCTop: TrDepsCohs P K)
  {p k} {dc: DepsCohs p k}
  (c0: DepsCohsChain (trDepsCohsA TCTop) dc):
  {TC: TrDepsCohs p k &T {C: TrCohsChain TCTop TC &T
    ((dc; c0): {dc0: DepsCohs p k &T
       DepsCohsChain (trDepsCohsA TCTop) dc0}) =
    (trDepsCohsA TC; trCohsChainA C)}}.
Proof.
  induction c0 as [|p k dc' c0' IH].
  - now exact (TCTop; (TrCohsChainNil; eq_refl)).
  - destruct IH as (TC', (C', e')).
    refine (proj1TrDepsCohs TC'; (TrCohsChainCons C'; _)).
    now exact (f_equal (fun s: {dc0: DepsCohs p.+1 k &T
        DepsCohsChain (trDepsCohsA TCTop) dc0} =>
      ((proj1DepsCohs s.1; DepsCohsChainCons s.2):
        {dc0: DepsCohs p k.+1 &T
          DepsCohsChain (trDepsCohsA TCTop) dc0})) e').
Qed.

(** Normal forms of chain packages

    The [B]-side of the round trip compares [g]'s fuel-synthesized chains
    with the [B]-images of lifted translation chains; both are iterated
    [dcStep]s of the nil package, reconnected through length/stage
    arithmetic alone. *)

Fixpoint dcStepIter {P K} {dcTop: DepsCohs P K} (j: nat)
  (s: DCPack dcTop): DCPack dcTop :=
  match j with
  | 0 => s
  | S j => dcStep (dcStepIter j s)
  end.

Lemma chain2DownIter {P K} (T2: DepsCohs2 P K) (j: nat):
  dc2PackDeps (chain2Down T2 j) =
  dcStepIter j (P; (K; (T2.(_depsCohs); DepsCohsChainNil))).
Proof.
  induction j; cbn [chain2Down dcStepIter].
  - now reflexivity.
  - now rewrite dc2PackDepsStep, IHj.
Qed.

Fixpoint trCohsChainLen {P K} {TCTop: TrDepsCohs P K}
  {p k} {TC: TrDepsCohs p k} (C: TrCohsChain TCTop TC): nat :=
  match C with
  | TrCohsChainNil => 0
  | TrCohsChainCons C' => (trCohsChainLen C').+1
  end.

Lemma trCohsChainStage {P K} {TCTop: TrDepsCohs P K}
  {p k} {TC: TrDepsCohs p k} (C: TrCohsChain TCTop TC):
  p + trCohsChainLen C = P.
Proof.
  induction C as [|p k TC C IH]; cbn [trCohsChainLen].
  - now symmetry; apply plus_n_O.
  - rewrite <- plus_n_Sm. now exact IH.
Qed.

Lemma trChainPackB {P K} {TCTop: TrDepsCohs P K}
  {p k} {TC: TrDepsCohs p k} (C: TrCohsChain TCTop TC):
  ((p; (k; (trDepsCohsB TC; trCohsChainB C))): DCPack (trDepsCohsB TCTop)) =
  dcStepIter (trCohsChainLen C)
    (P; (K; (trDepsCohsB TCTop; DepsCohsChainNil))).
Proof.
  induction C as [|p k TC C IH]; cbn [trCohsChainLen dcStepIter].
  - now reflexivity.
  - now rewrite <- IH.
Qed.


(** The candidate-filler contraction: given a frame
    translation [tr], an identification [HF] of the cells with the total
    space, and the frame identification [FRT] ([pshF] of a cell is the
    translation of its frame), the candidate filler over a translated
    frame is equivalent to the original filler. The construction composes
    existing equivalences, and [UIP] identifies their path components. *)

Definition fillerEquivOf {FrB FrA CellH: HSet} (tr: Equiv FrB FrA)
  {E: FrB -> HSet} (HF: CellH = {D: FrB & E D})
  (pshF: CellH -> FrA)
  (FRT: forall (D: FrB) (c: E D),
    pshF (rew [Dom] (eq_sym HF) in ((D; c): ({D0: FrB & E D0}: HSet)))
      = tr D)
  (D: FrB):
  Equiv {cell: CellH &T tr D = pshF cell} (E D) :=
  compEquiv
    (sigTEquivSnd (fun cell => pathEquiv (A := FrA)
      (fun q => q • f_equal pshF (eq_sym (rew_sym_cancel (P := Dom) HF cell)))
      (fun q => q • f_equal pshF (rew_sym_cancel (P := Dom) HF cell))))
  (compEquiv
    (sigTEquivFst (rewEquiv (fun h: HSet => h.(Dom)) HF))
  (compEquiv
    (sigTEquivSnd (fun t => pathEquiv (A := FrA)
      (fun q => q • FRT t.1 t.2)
      (fun q => q • eq_sym (FRT t.1 t.2))))
  (compEquiv
    (sigTEquivSnd (fun t => pathEquiv2 (eqvInj tr)
      (fun q => f_equal tr q)))
    (baseContract E D)))).

(** The inverse of the contraction, whole: the pair of the candidate frame
    of a transported cell with its tautological filler is the translated
    pair — the single equation the [FRT] step consumes. *)

Lemma fillerEquivOfWhole {FrB FrA CellH: HSet} (tr: Equiv FrB FrA)
  {E: FrB -> HSet} (HF: CellH = {D: FrB & E D})
  (pshF: CellH -> FrA)
  (FRT: forall (D: FrB) (c: E D),
    pshF (rew [Dom] (eq_sym HF) in ((D; c): ({D0: FrB & E D0}: HSet)))
      = tr D)
  (D: FrB) (c: E D):
  ((pshF (rew [Dom] (eq_sym HF) in ((D; c): ({D0: FrB & E D0}: HSet)));
    (rew [Dom] (eq_sym HF) in ((D; c): ({D0: FrB & E D0}: HSet)); eq_refl))
   : {D0: FrA &T {cell: CellH &T D0 = pshF cell}})
  = (tr D; symEquiv (fillerEquivOf tr HF pshF FRT D) c).
Proof.
  refine (eq_existT_curried (FRT D c) _).
  cbn.
  etransitivity.
  { now exact (rew_sigT_fst_const (FRT D c) _ eq_refl). }
  apply f_equal.
  now apply FrA.(UIP).
Qed.

Lemma gFaceLevelEq {m0} {Xpre0: (νSetAt m0).(prefix)} (X0: νSetFrom m0 Xpre0)
  {n1 n2: nat} (e: n1 = n2) (dim: nat)
  (H1: dim <= n1 + m0) (H2: dim <= n2 + m0) (ε: arity)
  (d: gF0 X0 n1.+1):
  gFace X0 n2 dim H2 ε (rew [fun l => (gF0 X0 l.+1).(Dom)] e in d) =
  rew [fun l => (gF0 X0 l).(Dom)] e in gFace X0 n1 dim H1 ε d.
Proof.
  now destruct e.
Qed.

(** The descent identification

    The corecursive body of [fg] must, at an abstract level, identify the
    cells of [g X] with the total spaces of the carried [X]-position.
    Induction on [Desc] proves this identification, with [plus_n_Sm]-style
    equalities on the relative index at each successor step. *)

Section FG.

Variable X: νSets.

Inductive Desc: forall {n} {Xpre: (νSetAt n).(prefix)},
  νSetFrom n Xpre -> Type :=
| DescZ: Desc X
| DescS {n} {Xpre: (νSetAt n).(prefix)} {S0: νSetFrom n Xpre}:
    Desc S0 -> Desc (S0.(next _ _)).

(** Indexing by [k + n] makes the use sites instantiate [k := 0]. The
    branches supply the required [plus_n_O] and [plus_n_Sm] equalities. *)

Fixpoint descF0 {n} {Xpre: (νSetAt n).(prefix)} {S0: νSetFrom n Xpre}
  (D: Desc S0) (k: nat) {struct D}: gF0 X (k + n) = gF0 S0 k :=
  match D in @Desc n0 _ S1 return gF0 X (k + n0) = gF0 S1 k with
  | DescZ => f_equal (gF0 X) (eq_sym (plus_n_O k))
  | @DescS n1 _ S1 D' =>
      f_equal (gF0 X) (eq_sym (plus_n_Sm k n1)) • descF0 D' k.+1
  end.

(** At [k := 0], the cells of [g X] at the position's level are the
    total space of the position — the corecursive state's cell
    identification. *)

Definition descTotal {n} {Xpre: (νSetAt n).(prefix)} {S0: νSetFrom n Xpre}
  (D: Desc S0): gF0 X n = νTotal S0 := descF0 D 0.

(** The faces of [g X] along a descent are the faces of the position:
    the face-compatibility of the cell identification, by induction on
    the witness with index equalities normalized by [natUIP]. *)

Lemma descFace {n} {Xpre: (νSetAt n).(prefix)} {S0: νSetFrom n Xpre}
  (D: Desc S0) (k dim: nat) (HdX: dim <= k + n) (HdS: dim <= k + n)
  (ε: arity) (t: gF0 S0 k.+1):
  (g X).(Face) (k + n) dim HdX ε
    (rew [Dom] (eq_sym (descF0 D k.+1)) in t) =
  rew [Dom] (eq_sym (descF0 D k)) in (gFace S0 k dim HdS ε t).
Proof.
  revert k dim HdX HdS ε t; induction D; intros k dim HdX HdS ε t.
  - cbn [descF0].
    rewrite 2 eq_sym_f_equal.
    rewrite (natUIP (eq_sym (eq_sym (plus_n_O k))) (plus_n_O k)).
    rewrite (natUIP (eq_sym (eq_sym (plus_n_O k.+1)))
      (f_equal S (plus_n_O k))).
    rewrite <- 2 (rew_map (fun h: HSet => h.(Dom)) (gF0 X)).
    rewrite <- (rew_map (fun l => (gF0 X l).(Dom)) S).
    now exact (gFaceLevelEq X (plus_n_O k) dim HdS
      (leR_eq_r (plus_n_O (k + 0)) HdX) ε t).
  - cbn [descF0].
    rewrite 2 eq_trans_sym_distr.
    rewrite 2 eq_sym_f_equal.
    rewrite (natUIP (eq_sym (eq_sym (plus_n_Sm k n))) (plus_n_Sm k n)).
    rewrite (natUIP (eq_sym (eq_sym (plus_n_Sm k.+1 n)))
      (f_equal S (plus_n_Sm k n))).
    rewrite <- 2 rew_compose.
    rewrite <- 2 (rew_map (fun h: HSet => h.(Dom)) (gF0 X)).
    rewrite <- (rew_map (fun l => (gF0 X l).(Dom)) S).
    refine (gFaceLevelEq X (plus_n_Sm k n) dim
      (leR_eq_r (eq_sym (plus_n_Sm k n) • plus_n_O (k + n).+1) HdS)
      (leR_eq_r (plus_n_O (k + n.+1)) HdX) ε _ • _).
    now exact (f_equal
      (fun w => rew [fun l => (gF0 X l).(Dom)] plus_n_Sm k n in w)
      (IHD k.+1 dim (leR_eq_r (eq_sym (plus_n_Sm k n)) HdS)
        (leR_eq_r (eq_sym (plus_n_Sm k n)) HdS) ε t)).
Qed.

(** Aligning the two presentations of the next-level cell identification:
    stepping the witness, then identifying at relative index 0, is
    identifying at relative index 1. [natUIP] identifies the resulting
    [plus_n_Sm] equality with the required index equality. *)

Lemma descTotalS {n} {Xpre: (νSetAt n).(prefix)} {S0: νSetFrom n Xpre}
  (HD: Desc S0): descTotal (DescS HD) = descF0 HD 1.
Proof.
  unfold descTotal; cbn [descF0].
  rewrite (natUIP (eq_sym (plus_n_Sm 0 n)) eq_refl).
  now apply eq_trans_refl_l.
Qed.

(** The carried frame identification: the candidate
    frame of a cell transported from the position's total space is the
    translated frame. Stated in the exact shape [fillerEquivOf] consumes. *)

Definition FrtInv {m} {XpreA XpreB: (νSetAt m.+1).(prefix)}
  (T: PshTower (g X) m XpreA) (SB: νSetFrom m.+1 XpreB)
  (HD: Desc SB) (W: TrTower m.+1 XpreA XpreB): Type :=
  forall (D: mkFrame (νTowerDeps XpreB)) (c: SB.(this _ _) D),
  mkPshFrame (g X) (towerPshDeps (g X) T)
    (rew [Dom] (eq_sym (descTotal HD)) in
      ((D; c): ({D0: mkFrame (νTowerDeps XpreB) & SB.(this _ _) D0}: HSet)))
  = mkFrameEqv (towerTrDeps W) D.

(** The filler equivalence of the round trip at a level: the inverse of
    the candidate-filler contraction over the frame identification. *)

Definition fgThis {m} {XpreA XpreB: (νSetAt m.+1).(prefix)}
  (T: PshTower (g X) m XpreA) (SB: νSetFrom m.+1 XpreB)
  (HD: Desc SB) (W: TrTower m.+1 XpreA XpreB) (FRT: FrtInv T SB HD W):
  forall D: mkFrame (νTowerDeps XpreB),
  Equiv (SB.(this _ _) D)
    (mkPshFiller (g X) (towerPshDeps (g X) T) (mkFrameEqv (towerTrDeps W) D))
  := fun D => symEquiv (fillerEquivOf (mkFrameEqv (towerTrDeps W))
       (descTotal HD) (mkPshFrame (g X) (towerPshDeps (g X) T)) FRT D).

(** The bottom face of [g X] at the position, as [νFace] along the
    [B]-image of a lifted translation chain: the fuel-synthesized package
    and the image package are both [dcStep]-iterations of the nil package,
    of the same length by the stage equation. *)

Lemma fgFaceB {m} {XpreA XpreB: (νSetAt m.+1).(prefix)}
  (W: TrTower m.+1 XpreA XpreB) (SB: νSetFrom m.+1 XpreB)
  {EA: mkFrame (νTowerDeps XpreA) -> HSet}
  (fEqv: forall d, Equiv (SB.(this _ _) d)
    (EA (mkFrameEqv (towerTrDeps W) d)))
  (rp: mkTrRestrPaintingTypes (towerTrDeps W)
    (TopTrDep (T := towerTrDeps W) fEqv)
    ((νDataAt XpreA).(restrPaintings) EA)
    ((νDataAt XpreB).(restrPaintings) (SB.(this _ _))))
  {p k} {TC: TrDepsCohs p k}
  (C: TrCohsChain (trTowerDepsCohs W fEqv rp) TC)
  (Hp: p <= m.+1) (ε: arity) (t: νTotal (SB.(next _ _))):
  gFace SB 0 p Hp ε t = νFace (trCohsChainB C) ε t.1.
Proof.
  change (νFaceFuel SB (m.+1 - p) ε t = νFace (trCohsChainB C) ε t.1).
  unfold νFaceFuel.
  rewrite (f_equal (fun z => z - p) (eq_sym (trCohsChainStage C))
    • addSubCancelL p (trCohsChainLen C)).
  now exact (f_equal
    (fun s: DCPack (νDepsCohsAt SB) => νFace s.2.2.2 ε t.1)
    (chain2DownIter (νDepsCohs2At SB) (trCohsChainLen C)
      • eq_sym (trChainPackB C))).
Qed.

(** The step of the frame identification, by [νFaceEq]: every face of the
    two frames agrees. Lift the arbitrary chain to the two equipped sides,
    rewrite [νFace] with [pshνFace] and [νFaceTr], identify the transported
    face with the face at the position using [descFace] and [fgFaceB], and
    apply the current identification through [fillerEquivOfWhole]. *)

Lemma fgFrameStep {m} {XpreA XpreB: (νSetAt m.+1).(prefix)}
  (T: PshTower (g X) m XpreA) (rpPsh: PshTowerRestrPaintings (g X) T)
  (SB: νSetFrom m.+1 XpreB) (HD: Desc SB)
  (W: TrTower m.+1 XpreA XpreB) (FRT: FrtInv T SB HD W)
  (rpTr: mkTrRestrPaintingTypes (towerTrDeps W)
    (TopTrDep (T := towerTrDeps W) (fgThis T SB HD W FRT))
    ((νDataAt XpreA).(restrPaintings)
      (mkPshFiller (g X) (towerPshDeps (g X) T)))
    ((νDataAt XpreB).(restrPaintings) (SB.(this _ _)))):
  FrtInv (towerStep (g X) T rpPsh) (SB.(next _ _)) (DescS HD)
    (trTowerStep W (fgThis T SB HD W FRT) rpTr).
Proof.
  intros D c.
  refine (νFaceEq
    (dcTop := pshDepsCohs (g X) (towerPshDepsCohs (g X) T rpPsh)) _ _ _).
  intros p k dc c0 ε.
  destruct (pshChainLift (g X) (towerPshDepsCohs (g X) T rpPsh) c0)
    as (PC, (Cpsh, ePsh)).
  destruct (trChainLift (trTowerDepsCohs W (fgThis T SB HD W FRT) rpTr) c0)
    as (TC, (Ctr, eTr)).
  pose (Hp := leR_eq_r (trCohsChainStage Ctr)
    (leR_add_r p (trCohsChainLen Ctr))).
  refine (f_equal (fun s: {dc0: DepsCohs p k &T
      DepsCohsChain (pshDepsCohs (g X) (towerPshDepsCohs (g X) T rpPsh)) dc0}
    => νFace s.2 ε _) ePsh • _).
  refine (_ • eq_sym (f_equal (fun s: {dc0: DepsCohs p k &T
      DepsCohsChain (pshDepsCohs (g X) (towerPshDepsCohs (g X) T rpPsh)) dc0}
    => νFace s.2 ε _) eTr)).
  rewrite (pshνFace (g X) Cpsh Hp ε).
  rewrite (νFaceTr Ctr ε D).
  rewrite (descTotalS HD).
  rewrite (descFace HD 0 p Hp Hp ε (D; c)).
  rewrite (fgFaceB W SB (fgThis T SB HD W FRT) rpTr Ctr Hp ε (D; c)).
  now exact (fillerEquivOfWhole (mkFrameEqv (towerTrDeps W)) (descTotal HD)
    (mkPshFrame (g X) (towerPshDeps (g X) T)) FRT
    (νFace (trCohsChainB Ctr) ε D).1 (νFace (trCohsChainB Ctr) ε D).2).
Qed.

(** Base case of the frame identification. At level 0, the frame is
    [unit], the candidate frame map is constant, and [hunit_ext] proves
    the required identification. *)

Definition pshF0A: gF0 X 0 ->
  mkFrame (νTowerDeps (tt: (νSetAt 0).(prefix))) := fun _ => tt.

Definition frt0 (D: mkFrame (νTowerDeps (tt: (νSetAt 0).(prefix))))
  (c: X.(this _ _) D):
  pshF0A (rew [Dom] (eq_sym (descTotal DescZ)) in
    ((D; c): ({D0: mkFrame (νTowerDeps (tt: (νSetAt 0).(prefix))) &
       X.(this _ _) D0}: HSet)))
  = mkFrameEqv (towerTrDeps trTower0) D :=
  hunit_ext tt (mkFrameEqv (towerTrDeps trTower0) D).

Definition fgThis0:
  forall D: mkFrame (νTowerDeps (tt: (νSetAt 0).(prefix))),
  Equiv (X.(this _ _) D)
    (pshFiller0 (g X) (mkFrameEqv (towerTrDeps trTower0) D)) :=
  fun D => symEquiv (fillerEquivOf (mkFrameEqv (towerTrDeps trTower0))
    (descTotal DescZ) pshF0A frt0 D).

(** The level-1 base case of [fgFrameStep]. The only chain from stage 0 is
    empty, so both applications of [νFace] reduce by conversion. *)

Lemma fgFrameStep0:
  FrtInv (tower1 (g X)) (X.(next _ _)) (DescS DescZ)
    (trTowerStep trTower0 fgThis0 tt).
Proof.
  intros D c.
  refine (νFaceEq
    (dcTop := trDepsCohsA (trTowerDepsCohs trTower0 fgThis0 tt)) _ _ _).
  intros p k dc c0 ε.
  destruct c0 as [|p k dc' c0'].
  2: { pose proof (cohsChainStage c0') as HS. now discriminate HS. }
  rewrite (νFaceTr (TCTop := trTowerDepsCohs trTower0 fgThis0 tt)
    TrCohsChainNil ε D).
  unfold νFace.
  rewrite nth_lam.
  rewrite (descTotalS DescZ).
  rewrite (descFace DescZ 0 0 leR_O leR_O ε (D; c)).
  now exact (fillerEquivOfWhole (mkFrameEqv (towerTrDeps trTower0))
    (descTotal DescZ) pshF0A frt0
    (νFace (dcTop := νDepsCohsAt X) DepsCohsChainNil ε D).1
    (νFace (dcTop := νDepsCohsAt X) DepsCohsChainNil ε D).2).
Qed.

(** The corecursion

    The state is the pair of tower states with the descent witness, the
    frame identification, and the restr-painting commutations at the
    filler equivalence it induces; every component steps by its own step
    lemma, and the filler equivalence is the contraction. *)

CoFixpoint fgGen {m} {XpreA XpreB: (νSetAt m.+1).(prefix)}
  (T: PshTower (g X) m XpreA) (rpPsh: PshTowerRestrPaintings (g X) T)
  (SB: νSetFrom m.+1 XpreB) (HD: Desc SB)
  (W: TrTower m.+1 XpreA XpreB) (FRT: FrtInv T SB HD W)
  (rpTr: mkTrRestrPaintingTypes (towerTrDeps W)
    (TopTrDep (T := towerTrDeps W) (fgThis T SB HD W FRT))
    ((νDataAt XpreA).(restrPaintings)
      (mkPshFiller (g X) (towerPshDeps (g X) T)))
    ((νDataAt XpreB).(restrPaintings) (SB.(this _ _)))):
  νSetFromEquiv W (pshNext (g X) m XpreA T rpPsh) SB :=
  trCons _ _ _ W (pshNext (g X) m XpreA T rpPsh) SB
    (fgThis T SB HD W FRT)
    rpTr
    (fgGen (towerStep (g X) T rpPsh) (towerStepRestrPaintings (g X) T rpPsh)
      (SB.(next _ _)) (DescS HD)
      (trTowerStep W (fgThis T SB HD W FRT) rpTr)
      (fgFrameStep T rpPsh SB HD W FRT rpTr)
      (mkTrRestrPaintings (TopTrCohDep
        (TC := trTowerDepsCohs W (fgThis T SB HD W FRT) rpTr)
        (fgThis (towerStep (g X) T rpPsh) (SB.(next _ _)) (DescS HD)
          (trTowerStep W (fgThis T SB HD W FRT) rpTr)
          (fgFrameStep T rpPsh SB HD W FRT rpTr))))).

Definition fg: νSetFromEquiv trTower0 (f (g X)) X :=
  trCons _ _ _ trTower0 (f (g X)) X
    fgThis0
    tt
    (fgGen (tower1 (g X)) (tower1RestrPaintings (g X))
      (X.(next _ _)) (DescS DescZ)
      (trTowerStep trTower0 fgThis0 tt)
      fgFrameStep0
      (mkTrRestrPaintings (TopTrCohDep
        (TC := trTowerDepsCohs trTower0 fgThis0 tt)
        (fgThis (tower1 (g X)) (X.(next _ _)) (DescS DescZ)
          (trTowerStep trTower0 fgThis0 tt) fgFrameStep0)))).

End FG.

End νSetRoundtrip.

Module νSetRoundtripSimplicial := νSetRoundtrip SimplicialLayer.
Module νSetRoundtripCubical := νSetRoundtrip CubicalLayer.
