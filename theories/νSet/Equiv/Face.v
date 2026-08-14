(** Face operations on the indexed side.

    The face maps are derived from frame projection and painting extension.
    These operations recurse on endpoint-indexed chains connecting stages of the
    dependency construction.

    The construction uses relative indices: a stage [p] under an ambient
    dimension [n] is represented by the difference [k := n - p]. Descending
    changes both indices, and for open [p] the landing stage after several steps
    cannot be expressed by reducing a subtraction. A chain records that landing
    stage in its endpoint index. The endpoint index directly determines the
    result type of the recursion. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp Notation νSet.Layer νSet.
From Bonak Require νSetEquiv.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module Face (A: LayerSig).
Import A.

Module Export νSetEquiv := Bonak.νSet.Equiv.νSetEquiv.νSetEquiv A.

(** Chains of projections between frame stages *)

Inductive DepsChain {P K} (depsTop: DepsRestr P K):
  forall {p k}, DepsRestr p k -> Type :=
| DepsChainNil: DepsChain depsTop depsTop
| DepsChainCons {p k} {deps: DepsRestr p.+1 k}:
    DepsChain depsTop deps -> DepsChain depsTop deps.(1).

Arguments DepsChainNil {P K depsTop}.
Arguments DepsChainCons {P K depsTop p k deps} _.

(** [getFrame]: project a frame down along a chain — iterated first
    projection. *)

Fixpoint getFrame {P K} {depsTop: DepsRestr P K} {p k} {deps: DepsRestr p k}
  (c: DepsChain depsTop deps): mkFrame depsTop -> mkFrame deps :=
  match c with
  | DepsChainNil => fun d => d
  | DepsChainCons c' => fun d => (getFrame c' d).1
  end.

Fixpoint chainCompose {P K} {depsTop: DepsRestr P K}
  {p k} {depsMid: DepsRestr p k} {p' k'} {deps: DepsRestr p' k'}
  (c1: DepsChain depsTop depsMid) (c2: DepsChain depsMid deps):
  DepsChain depsTop deps :=
  match c2 with
  | DepsChainNil => c1
  | DepsChainCons c2' => DepsChainCons (chainCompose c1 c2')
  end.

(** [getFrame] is functorial in the chain: projecting along [c1] and then
    along [c2] is projecting along their composite. *)

Lemma getFrameCompose {P K} {depsTop: DepsRestr P K}
  {p k} {depsMid: DepsRestr p k} {p' k'} {deps: DepsRestr p' k'}
  (c1: DepsChain depsTop depsMid) (c2: DepsChain depsMid deps)
  (d: mkFrame depsTop):
  getFrame c2 (getFrame c1 d) = getFrame (chainCompose c1 c2) d.
Proof.
  induction c2.
  - now reflexivity.
  - cbn. now rewrite IHc2.
Defined.

(** Chains of climbs through painting extensions *)

Inductive ExtChain {P K} {depsTop: DepsRestr P K}
  (extTop: DepsRestrExtension P K depsTop):
  forall {p k} {deps: DepsRestr p k}, DepsRestrExtension p k deps -> Type :=
| ExtChainNil: ExtChain extTop extTop
| ExtChainCons {p k} {deps: DepsRestr p.+1 k}
    {ext: DepsRestrExtension p.+1 k deps}:
    ExtChain extTop ext -> ExtChain extTop (AddRestrDep deps ext).

Arguments ExtChainNil {P K depsTop extTop}.
Arguments ExtChainCons {P K depsTop extTop p k deps ext} _.

(** [getPainting]: rebuild a cell at the top of the chain from a frame and
    a painting over it, moving layers from the painting to the frame. *)

Fixpoint getPainting {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext):
  forall (d: mkFrame deps), mkPainting ext d ->
  { d': mkFrame depsTop &T mkPainting extTop d' } :=
  match c with
  | ExtChainNil => fun d cp => (d; cp)
  | ExtChainCons c' => fun d cp => getPainting c' (d; cp.1) cp.2
  end.

Fixpoint extChainCompose {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {depsMid: DepsRestr p k} {extMid: DepsRestrExtension p k depsMid}
  {p' k'} {deps: DepsRestr p' k'} {ext: DepsRestrExtension p' k' deps}
  (c1: ExtChain extTop extMid) (c2: ExtChain extMid ext):
  ExtChain extTop ext :=
  match c2 with
  | ExtChainNil => c1
  | ExtChainCons c2' => ExtChainCons (extChainCompose c1 c2')
  end.

(** The frame chain underlying a painting chain. *)

Fixpoint extChainDeps {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext): DepsChain depsTop deps :=
  match c with
  | ExtChainNil => DepsChainNil
  | ExtChainCons c' => DepsChainCons (extChainDeps c')
  end.

(** The rebuilt cell projects back onto the frame it was built from. *)

Lemma getFrameGetPainting {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext) (d: mkFrame deps) (cp: mkPainting ext d):
  getFrame (extChainDeps c) (getPainting c d cp).1 = d.
Proof.
  revert d cp; induction c; intros d cp.
  - now reflexivity.
  - cbn. now rewrite IHc.
Defined.

(** Projecting a rebuilt cell down to an intermediate stage rebuilds the
    cell only up to that stage. *)

Lemma getFrameGetPainting' {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {depsMid: DepsRestr p k} {extMid: DepsRestrExtension p k depsMid}
  {p' k'} {deps: DepsRestr p' k'} {ext: DepsRestrExtension p' k' deps}
  (c1: ExtChain extTop extMid) (c2: ExtChain extMid ext)
  (d: mkFrame deps) (cp: mkPainting ext d):
  getFrame (extChainDeps c1) (getPainting (extChainCompose c1 c2) d cp).1 =
  (getPainting c2 d cp).1.
Proof.
  revert d cp; induction c2; intros d cp.
  - cbn. now apply getFrameGetPainting.
  - cbn. now apply IHc2.
Defined.

(** Chains in the [DepsCohs] world

    A [DepsCohsChain] from the top of level n down to stage p induces,
    definitionally, the level-(n+1) frame descent ([cohsChainNext], through
    [mkDepsRestr]) and the level-n painting climb ([cohsChainExt]) — so a
    single chain supplies both witnesses the face maps need, at their two
    adjacent levels. *)

Inductive DepsCohsChain {P K} (dcTop: DepsCohs P K):
  forall {p k}, DepsCohs p k -> Type :=
| DepsCohsChainNil: DepsCohsChain dcTop dcTop
| DepsCohsChainCons {p k} {dc: DepsCohs p.+1 k}:
    DepsCohsChain dcTop dc -> DepsCohsChain dcTop (proj1DepsCohs dc).

Arguments DepsCohsChainNil {P K dcTop}.
Arguments DepsCohsChainCons {P K dcTop p k dc} _.

Fixpoint cohsChainExt {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc):
  ExtChain dcTop.(_extraDeps) dc.(_extraDeps) :=
  match c with
  | DepsCohsChainNil => ExtChainNil
  | DepsCohsChainCons c' => ExtChainCons (cohsChainExt c')
  end.

Fixpoint cohsChainNext {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc):
  DepsChain (mkDepsRestr (depsCohs := dcTop)) (mkDepsRestr (depsCohs := dc)) :=
  match c with
  | DepsCohsChainNil => DepsChainNil
  | DepsCohsChainCons c' => DepsChainCons (cohsChainNext c')
  end.

Fixpoint cohsChainDeps {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc): DepsChain dcTop.(_deps) dc.(_deps) :=
  match c with
  | DepsCohsChainNil => DepsChainNil
  | DepsCohsChainCons c' => DepsChainCons (cohsChainDeps c')
  end.

Fixpoint cohsChainNext1 {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc):
  DepsChain (mkDepsRestr (depsCohs := dcTop)).(1)
            (mkDepsRestr (depsCohs := dc)).(1) :=
  match c with
  | DepsCohsChainNil => DepsChainNil
  | DepsCohsChainCons c' => DepsChainCons (cohsChainNext1 c')
  end.

Fixpoint cohsChainCompose {P K} {dcTop: DepsCohs P K}
  {p k} {dcMid: DepsCohs p k} {p' k'} {dc: DepsCohs p' k'}
  (c1: DepsCohsChain dcTop dcMid) (c2: DepsCohsChain dcMid dc):
  DepsCohsChain dcTop dc :=
  match c2 with
  | DepsCohsChainNil => c1
  | DepsCohsChainCons c2' => DepsCohsChainCons (cohsChainCompose c1 c2')
  end.

(** The length of a chain is the offset of the restriction it commutes
    with ([getFrameRestr]); it is bounded by the codomain's [k]. *)

Fixpoint cohsChainLen {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc): nat :=
  match c with
  | DepsCohsChainNil => 0
  | DepsCohsChainCons c' => (cohsChainLen c').+1
  end.

Fixpoint cohsChainLe {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc): cohsChainLen c <= k :=
  match c with
  | DepsCohsChainNil => leR_O
  | DepsCohsChainCons c' => ⇑ (cohsChainLe c')
  end.

(** Pushing a second-order extension down a chain, and the induced
    painting chain one level up. *)

Fixpoint cohsChainExtend {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc) (X: DepsCohsExtension P K dcTop):
  DepsCohsExtension p k dc :=
  match c with
  | DepsCohsChainNil => X
  | DepsCohsChainCons c' => AddCohDep _ (cohsChainExtend c' X)
  end.

Fixpoint cohsChainNextExt {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc) (X: DepsCohsExtension P K dcTop):
  ExtChain (mkExtraDeps X) (mkExtraDeps (cohsChainExtend c X)) :=
  match c with
  | DepsCohsChainNil => ExtChainNil
  | DepsCohsChainCons c' => ExtChainCons (cohsChainNextExt c' X)
  end.

(** The face maps of the indexed construction

    Given a full frame [d] one level up, project it down to
    stage p+1, take the ε-component of its top layer — a painting over the
    restricted frame at stage p — and rebuild a full cell from it. This is
    the [Face] operation of the presheaf associated to a [νSet]. *)

Definition νFace {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := dcTop))):
  { d': mkFrame dcTop.(_deps) &T mkPainting dcTop.(_extraDeps) d' } :=
  getPainting (cohsChainExt c)
    (mkRestrFrame (depsCohs := dc) 0 leR_O ε (getFrame (cohsChainNext c) d).1)
    (nth (getFrame (cohsChainNext c) d).2 ε).

(** Commutation of the projections with the restrictions

    Restricting at the top-stage diagonal and projecting down equals
    projecting down one level up and restricting at the accumulated
    offset. *)

Lemma getFrameRestr {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := dcTop)).(1)):
  getFrame (cohsChainDeps c) (mkRestrFrame (depsCohs := dcTop) 0 leR_O ε d) =
  mkRestrFrame (depsCohs := dc) (cohsChainLen c) (cohsChainLe c) ε
    (getFrame (cohsChainNext1 c) d).
Proof.
  induction c.
  - now reflexivity.
  - cbn. now rewrite IHc.
Defined.

(** Reading the ε-layer after climbing to stage q+1 equals climbing the
    ε-restricted painting from stage p. *)

Lemma getPaintingRestr {P K} {dcTop: DepsCohs P K}
  {P' K'} {depsTopN: DepsRestr P' K'}
  {extTopN: DepsRestrExtension P' K' depsTopN}
  (cQ: ExtChain extTopN dcTop.(_extraDeps))
  (X: DepsCohsExtension P K dcTop)
  {p k} {dc: DepsCohs p k} (c: DepsCohsChain dcTop dc) (ε: arity):
  forall (d: mkFrame (mkDepsRestr (depsCohs := dc)).(1))
  (cp: mkPainting (AddRestrDep (mkDepsRestr (depsCohs := dc))
         (mkExtraDeps (cohsChainExtend c X))) d),
  getPainting cQ
    (mkRestrFrame (depsCohs := dcTop) 0 leR_O ε
      ((getPainting (ExtChainCons (cohsChainNextExt c X)) d cp).1).1)
    (nth
      ((getPainting (ExtChainCons (cohsChainNextExt c X)) d cp).1).2 ε) =
  getPainting (extChainCompose cQ (cohsChainExt c))
    (mkRestrFrame (depsCohs := dc) (cohsChainLen c) (cohsChainLe c) ε d)
    (mkRestrPainting (cohsChainExtend c X)
      (cohsChainLen c) (cohsChainLe c) ε d cp).
Proof.
  induction c; intros d cp.
  - now reflexivity.
  - now exact (IHc (d; cp.1) cp.2).
Defined.

(** The exchange law for the face maps

    [DepsCohs2Chain] descends through [DepsCohs2] stages and induces the
    level-(n+1) [DepsCohsChain] ([cohs2ChainCohs], through [mkDepsCohs] —
    definitional, since [mkDepsCohs] commutes with the projections) and
    the level-n one ([cohs2ChainDepsCohs]). *)

Inductive DepsCohs2Chain {P K} (dc2Top: DepsCohs2 P K):
  forall {p k}, DepsCohs2 p k -> Type :=
| DepsCohs2ChainNil: DepsCohs2Chain dc2Top dc2Top
| DepsCohs2ChainCons {p k} {dc2: DepsCohs2 p.+1 k}:
    DepsCohs2Chain dc2Top dc2 -> DepsCohs2Chain dc2Top (proj1DepsCohs2 dc2).

Arguments DepsCohs2ChainNil {P K dc2Top}.
Arguments DepsCohs2ChainCons {P K dc2Top p k dc2} _.

Fixpoint cohs2ChainCohs {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2):
  DepsCohsChain (mkDepsCohs dc2Top) (mkDepsCohs dc2) :=
  match c with
  | DepsCohs2ChainNil => DepsCohsChainNil
  | DepsCohs2ChainCons c' => DepsCohsChainCons (cohs2ChainCohs c')
  end.

Fixpoint cohs2ChainDepsCohs {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2):
  DepsCohsChain dc2Top.(_depsCohs) dc2.(_depsCohs) :=
  match c with
  | DepsCohs2ChainNil => DepsCohsChainNil
  | DepsCohs2ChainCons c' => DepsCohsChainCons (cohs2ChainDepsCohs c')
  end.

Fixpoint cohs2ChainCompose {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2Mid: DepsCohs2 p k} {p' k'} {dc2: DepsCohs2 p' k'}
  (c1: DepsCohs2Chain dc2Top dc2Mid) (c2: DepsCohs2Chain dc2Mid dc2):
  DepsCohs2Chain dc2Top dc2 :=
  match c2 with
  | DepsCohs2ChainNil => c1
  | DepsCohs2ChainCons c2' => DepsCohs2ChainCons (cohs2ChainCompose c1 c2')
  end.

(** Chain algebra: the images commute with composition and each other. *)

Lemma cohsChainExtCompose {P K} {dcTop: DepsCohs P K}
  {p k} {dcMid: DepsCohs p k} {p' k'} {dc: DepsCohs p' k'}
  (a: DepsCohsChain dcTop dcMid) (b: DepsCohsChain dcMid dc):
  cohsChainExt (cohsChainCompose a b) =
  extChainCompose (cohsChainExt a) (cohsChainExt b).
Proof.
  induction b; cbn; [now reflexivity | now rewrite IHb].
Defined.

Lemma cohsChainNextCompose {P K} {dcTop: DepsCohs P K}
  {p k} {dcMid: DepsCohs p k} {p' k'} {dc: DepsCohs p' k'}
  (a: DepsCohsChain dcTop dcMid) (b: DepsCohsChain dcMid dc):
  cohsChainNext (cohsChainCompose a b) =
  chainCompose (cohsChainNext a) (cohsChainNext b).
Proof.
  induction b; cbn; [now reflexivity | now rewrite IHb].
Defined.

Lemma extChainDepsExt {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc):
  extChainDeps (cohsChainExt c) = cohsChainDeps c.
Proof.
  induction c; cbn; [now reflexivity | now rewrite IHc].
Defined.

Lemma cohs2ChainDepsNext {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2):
  cohsChainDeps (cohs2ChainCohs c) = cohsChainNext (cohs2ChainDepsCohs c).
Proof.
  induction c; cbn; [now reflexivity | now rewrite IHc].
Defined.

Lemma cohs2ChainCohsCompose {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2Mid: DepsCohs2 p k} {p' k'} {dc2: DepsCohs2 p' k'}
  (c1: DepsCohs2Chain dc2Top dc2Mid) (c2: DepsCohs2Chain dc2Mid dc2):
  cohs2ChainCohs (cohs2ChainCompose c1 c2) =
  cohsChainCompose (cohs2ChainCohs c1) (cohs2ChainCohs c2).
Proof.
  induction c2; cbn; [now reflexivity | now rewrite IHc2].
Defined.

Lemma cohs2ChainDepsCohsCompose {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2Mid: DepsCohs2 p k} {p' k'} {dc2: DepsCohs2 p' k'}
  (c1: DepsCohs2Chain dc2Top dc2Mid) (c2: DepsCohs2Chain dc2Mid dc2):
  cohs2ChainDepsCohs (cohs2ChainCompose c1 c2) =
  cohsChainCompose (cohs2ChainDepsCohs c1) (cohs2ChainDepsCohs c2).
Proof.
  induction c2; cbn; [now reflexivity | now rewrite IHc2].
Defined.

Lemma getFrameNext1 {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc)
  (x: mkFrame (mkDepsRestr (depsCohs := dcTop))):
  (getFrame (cohsChainNext c) x).1 = getFrame (cohsChainNext1 c) x.1.
Proof.
  induction c; cbn; [now reflexivity | now rewrite IHc].
Defined.

Lemma cohs2ChainLenEq {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2):
  cohsChainLen (cohs2ChainCohs c) = cohsChainLen (cohs2ChainDepsCohs c).
Proof.
  induction c; cbn; [now reflexivity | now rewrite IHc].
Defined.

Lemma mkRestrFrameLenIrr {p k} {dc: DepsCohs p k} {q q'} (e: q = q')
  {Hq: q <= k} {Hq': q' <= k} (ε: arity)
  (x: mkFrame (mkDepsRestr (depsCohs := dc)).(1)):
  mkRestrFrame (depsCohs := dc) q Hq ε x =
  mkRestrFrame (depsCohs := dc) q' Hq' ε x.
Proof.
  destruct e. now reflexivity.
Defined.

(** The two-level specialization of [getPaintingRestr]; all index
    equalities hold by conversion. *)

Lemma getPaintingRestr2 {P K} {dc2Top: DepsCohs2 P K}
  {P' K'} {depsTopN: DepsRestr P' K'}
  {extTopN: DepsRestrExtension P' K' depsTopN}
  (cQ: ExtChain extTopN (dc2Top.(_depsCohs)).(_extraDeps))
  {p k} {dc2: DepsCohs2 p k} (c: DepsCohs2Chain dc2Top dc2) (ε: arity):
  forall (d: mkFrame (mkDepsRestr (depsCohs := dc2.(_depsCohs))).(1))
  (cp: mkPainting (AddRestrDep (mkDepsRestr (depsCohs := dc2.(_depsCohs)))
         (mkExtraDeps dc2.(_extraDepsCohs))) d),
  getPainting cQ
    (mkRestrFrame (depsCohs := dc2Top.(_depsCohs)) 0 leR_O ε
      ((getPainting (ExtChainCons (cohsChainExt (cohs2ChainCohs c))) d cp).1).1)
    (nth
      ((getPainting (ExtChainCons (cohsChainExt (cohs2ChainCohs c))) d cp).1).2
      ε) =
  getPainting (extChainCompose cQ (cohsChainExt (cohs2ChainDepsCohs c)))
    (mkRestrFrame (depsCohs := dc2.(_depsCohs))
      (cohsChainLen (cohs2ChainDepsCohs c))
      (cohsChainLe (cohs2ChainDepsCohs c)) ε d)
    (mkRestrPainting dc2.(_extraDepsCohs)
      (cohsChainLen (cohs2ChainDepsCohs c))
      (cohsChainLe (cohs2ChainDepsCohs c)) ε d cp).
Proof.
  induction c; intros d cp.
  - now reflexivity.
  - now exact (IHc (d; cp.1) cp.2).
Defined.

(** Shifting a restriction past the diagonal one, via the stored
    coherence — the layer of the shifted restricted frame is
    definitionally the transported restricted painting. *)

Lemma restrShiftPair {p k} {dc2: DepsCohs2 p k}
  {P' K'} {depsTopN: DepsRestr P' K'}
  {extTopN: DepsRestrExtension P' K' depsTopN}
  (E: ExtChain extTopN (dc2.(_depsCohs)).(_extraDeps))
  (q: nat) (Hq: q <= k) (ε ω: arity)
  (W: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc2)).(1)):
  getPainting E
    (mkRestrFrame (depsCohs := dc2.(_depsCohs)) q Hq ε
       (mkRestrFrame (depsCohs := proj1DepsCohs (mkDepsCohs dc2)) 0 leR_O ω
          W.1))
    (mkRestrPainting dc2.(_extraDepsCohs) q Hq ε
       (mkRestrFrame (depsCohs := proj1DepsCohs (mkDepsCohs dc2)) 0 leR_O ω
          W.1)
       (nth W.2 ω)) =
  getPainting E
    (mkRestrFrame (depsCohs := dc2.(_depsCohs)) 0 leR_O ω
       (mkRestrFrame (depsCohs := mkDepsCohs dc2) q Hq ε W).1)
    (nth (mkRestrFrame (depsCohs := mkDepsCohs dc2) q Hq ε W).2 ω).
Proof.
  refine (f_equal (fun z: {d0: mkFrame (dc2.(_depsCohs)).(_deps) &T
      mkPainting (dc2.(_depsCohs)).(_extraDeps) d0} =>
    getPainting E z.1 z.2)
    (eq_existT_curried
      ((mkDepsCohs dc2).(_cohs).2 q Hq 0 leR_O ε ω W.1) _)).
  symmetry. now exact (nth_lmap _ W.2 ω).
Qed.

(** The exchange law: erasing dimension q and then p equals erasing
    dimension p and then q+1, for p ≤ q. *)

Lemma νFaceCoh {P K} {dc2Top: DepsCohs2 P K}
  {p k} {dc2Q: DepsCohs2 p k} (c1: DepsCohs2Chain dc2Top dc2Q)
  {p' k'} {dc2P: DepsCohs2 p' k'} (c2: DepsCohs2Chain dc2Q dc2P)
  (ε ω: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs dc2Top))):
  νFace (cohs2ChainDepsCohs c1) ε
    ((νFace (DepsCohsChainCons (cohs2ChainCohs (cohs2ChainCompose c1 c2)))
       ω d).1) =
  νFace (cohs2ChainDepsCohs (cohs2ChainCompose c1 c2)) ω
    ((νFace (cohs2ChainCohs c1) ε d).1).
Proof.
  unfold νFace.
  rewrite cohs2ChainCohsCompose, cohs2ChainDepsCohsCompose.
  assert (A1: cohsChainExt (DepsCohsChainCons
      (cohsChainCompose (cohs2ChainCohs c1) (cohs2ChainCohs c2))) =
    extChainCompose (cohsChainExt (cohs2ChainCohs c1))
      (ExtChainCons (cohsChainExt (cohs2ChainCohs c2)))).
  { cbn. now rewrite cohsChainExtCompose. }
  rewrite A1.
  rewrite <- (cohs2ChainDepsNext c1).
  rewrite <- (extChainDepsExt (cohs2ChainCohs c1)).
  rewrite getFrameGetPainting'.
  rewrite (getPaintingRestr2 (cohsChainExt (cohs2ChainDepsCohs c1)) c2 ε).
  rewrite <- cohsChainExtCompose.
  rewrite cohsChainNextCompose.
  rewrite <- getFrameCompose.
  rewrite <- (cohs2ChainDepsNext c1).
  rewrite <- (extChainDepsExt (cohs2ChainCohs c1)).
  rewrite getFrameGetPainting.
  rewrite <- (cohs2ChainDepsNext c2).
  rewrite (getFrameRestr (cohs2ChainCohs c2) ε).
  rewrite <- getFrameNext1.
  rewrite getFrameCompose.
  rewrite <- (cohsChainNextCompose (cohs2ChainCohs c1) (cohs2ChainCohs c2)).
  rewrite (mkRestrFrameLenIrr (cohs2ChainLenEq c2)
    (Hq := cohsChainLe (cohs2ChainCohs c2))
    (Hq' := cohsChainLe (cohs2ChainDepsCohs c2)) ε).
  rewrite restrShiftPair.
  now reflexivity.
Qed.

(** A full frame is determined by its faces

    [getPaintingEq]: rebuilding cells is injective. [layerEqNth]:
    the ε-components of the layers of two projected frames agree along the
    frame equality whenever the ε-faces agree — the UIP collapse happens
    here, in the frame HSet. [frameEqStep] climbs one stage using
    [ext]; [frameEqDescend] descends a chain accumulating stages; and
    [νFaceEq] grounds the descent at the stage-0 frame, which is [unit]. *)

Lemma getPaintingEq {P K} {depsTop: DepsRestr P K}
  {extTop: DepsRestrExtension P K depsTop}
  {p k} {deps: DepsRestr p k} {ext: DepsRestrExtension p k deps}
  (c: ExtChain extTop ext) (d d': mkFrame deps)
  (cp: mkPainting ext d) (cp': mkPainting ext d'):
  getPainting c d cp = getPainting c d' cp' ->
  ((d; cp): {d0: mkFrame deps &T mkPainting ext d0}) = (d'; cp').
Proof.
  revert d d' cp cp'; induction c as [|p k deps ext c IHc];
    intros d d' cp cp' H.
  - now exact H.
  - now exact (f_equal (fun x: {d0: mkFrame deps &T mkPainting ext d0} =>
      ((x.1.1; (x.1.2; x.2)):
        {d0: mkFrame deps.(1) &T mkPainting (AddRestrDep deps ext) d0}))
      (IHc (d; cp.1) (d'; cp'.1) cp.2 cp'.2 H)).
Qed.

Lemma layerEqNth {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc)
  (d d': mkFrame (mkDepsRestr (depsCohs := dcTop))) (ε: arity)
  (H: (getFrame (cohsChainNext c) d).1 = (getFrame (cohsChainNext c) d').1)
  (Hface: νFace c ε d = νFace c ε d'):
  nth
    (rew [mkLayer mkRestrFrames] H in (getFrame (cohsChainNext c) d).2) ε =
  nth (getFrame (cohsChainNext c) d').2 ε.
Proof.
  pose proof (getPaintingEq (cohsChainExt c) _ _ _ _ Hface) as PE.
  etransitivity.
  { now exact (eq_sym (map_subst (P := mkLayer mkRestrFrames)
      (fun x l => nth l ε) H _)). }
  etransitivity.
  { now exact (rew_map (fun y => ((mkPaintings dc.(_extraDeps)).2 y).(Dom))
      (fun x => mkRestrFrames.2 0 leR_O ε x) H
      (nth (getFrame (cohsChainNext c) d).2 ε)). }
  etransitivity.
  { now exact (f_equal (fun e => rew [fun y =>
        ((mkPaintings dc.(_extraDeps)).2 y).(Dom)] e in
      nth (getFrame (cohsChainNext c) d).2 ε)
      ((mkFrame dc.(_deps)).(UIP) (g := projT1_eq PE))). }
  now exact (projT2_eq PE).
Qed.

Lemma frameEqStep {P K} {dcTop: DepsCohs P K} {p k} {dc: DepsCohs p k}
  (c: DepsCohsChain dcTop dc)
  (d d': mkFrame (mkDepsRestr (depsCohs := dcTop)))
  (Hfaces: forall ε, νFace c ε d = νFace c ε d')
  (H: (getFrame (cohsChainNext c) d).1 = (getFrame (cohsChainNext c) d').1):
  getFrame (cohsChainNext c) d = getFrame (cohsChainNext c) d'.
Proof.
  refine (eq_existT_curried H _).
  now exact (ext _ _ (fun θ => layerEqNth c d d' θ H (Hfaces θ))).
Qed.

Lemma frameEqDescend {P K} {dcTop: DepsCohs P K}
  (d d': mkFrame (mkDepsRestr (depsCohs := dcTop)))
  (Hfaces: forall p k (dc: DepsCohs p k) (c: DepsCohsChain dcTop dc) ε,
    νFace c ε d = νFace c ε d')
  {p k} {dc: DepsCohs p k} (c: DepsCohsChain dcTop dc):
  getFrame (cohsChainNext c) d = getFrame (cohsChainNext c) d' -> d = d'.
Proof.
  induction c as [|p k dc c IHc]; intro H.
  - now exact H.
  - apply IHc. now exact (frameEqStep c d d' (Hfaces _ _ _ c) H).
Qed.

Fixpoint fullCohsChainSig {P}: forall {K} (dcTop: DepsCohs P K),
  {k0: nat &T {dc0: DepsCohs 0 k0 &T DepsCohsChain dcTop dc0}} :=
  match P with
  | 0 => fun K dcTop => (K; (dcTop; DepsCohsChainNil))
  | S P' => fun K dcTop =>
      let s := fullCohsChainSig (proj1DepsCohs dcTop) in
      (s.1; (s.2.1;
        cohsChainCompose (DepsCohsChainCons DepsCohsChainNil) s.2.2))
  end.

Lemma νFaceEq {P K} {dcTop: DepsCohs P K}
  (d d': mkFrame (mkDepsRestr (depsCohs := dcTop)))
  (Hfaces: forall p k (dc: DepsCohs p k) (c: DepsCohsChain dcTop dc) ε,
    νFace c ε d = νFace c ε d'):
  d = d'.
Proof.
  pose (s := fullCohsChainSig dcTop).
  apply (frameEqDescend d d' Hfaces s.2.2).
  apply (frameEqStep s.2.2 d d' (Hfaces _ _ _ s.2.2)).
  now exact (hunit_ext _ _).
Qed.

End Face.

Module FaceSimplicial := Face SimplicialLayer.
Module FaceCubical := Face CubicalLayer.
