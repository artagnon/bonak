(** The backward direction of the correspondence between the fibred
    presentation ([Presheaf]) and the indexed construction ([νSet]):
    [g: νSets -> Presheaf].

    The presheaf reads off the tower directly: the total spaces of the
    ω-limit tower as [F0], [νFace] as the face maps, and [νFaceCoh]
    as the exchange law. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet LeSProp NatLemmas Notation νSet.Layer
  νSet Face Presheaf νSetOfPresheaf Limit.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module PresheafOfνSet (A: LayerSig).
Import A.

Module Export νSetOfPresheaf := νSetOfPresheaf.νSetOfPresheaf A.

(** The tower data at a position

    [νSetFrom m Xpre] holds the fillers of all levels [>= m] over the prefix
    [Xpre]. The [νSetData] at the position ([νDataAt], from [νSetEquiv.v]),
    together with the current and next fillers, assembles the
    [DepsCohs]/[DepsCohs2] that the face operations of [Face.v] consume;
    [mkDepsCohs] of the latter is definitionally the former one level up. *)

Definition νDepsCohsAt {m} {Xpre: (νSetAt m).(prefix)}
  (X: νSetFrom m Xpre): DepsCohs m 0 := {|
  _deps := toDepsRestr (νDataAt Xpre).(restrFrames);
  _extraDeps := TopRestrDep (this X);
  _restrPaintings := (νDataAt Xpre).(restrPaintings) (this X);
  _cohs := (νDataAt Xpre).(cohFrames) (this X);
|}.

Definition νDepsCohs2At {m} {Xpre: (νSetAt m).(prefix)}
  (X: νSetFrom m Xpre): DepsCohs2 m 0 := {|
  _depsCohs := νDepsCohsAt X;
  _extraDepsCohs := TopCohDep (this (next X));
  _cohPaintings := (νDataAt Xpre).(cohPaintings) (this X)
    (this (next X));
|}.

Definition νTotal {m} {Xpre: (νSetAt m).(prefix)} (X: νSetFrom m Xpre):
  HSet :=
  {D: mkFrame (toDepsRestr (νDataAt Xpre).(restrFrames)) & (this X) D}.

(** [F0]: the total spaces down the tower *)

Fixpoint gF0 {m} {Xpre: (νSetAt m).(prefix)} (X: νSetFrom m Xpre)
  (n: nat): HSet :=
  match n with
  | 0 => νTotal X
  | S n => gF0 (next X) n
  end.

(** Chain synthesis

    [Face.v]'s operations take chains, which carry the number of stages to
    descend. The [Presheaf] interface supplies only an SProp bound [q <= n], and
    nothing can be extracted from it. So [g] synthesizes the chains from the
    fuel [level - dim]: [chain2Down] descends a [DepsCohs2Chain] from a top
    [DepsCohs2] by [j] stages (stalling at stage 0), packaged with its endpoint. *)

Definition Chain2Pack {P K} (dc2Top: DepsCohs2 P K): Type :=
  {p: nat &T {k: nat &T {dc2: DepsCohs2 p k &T DepsCohs2Chain dc2Top dc2}}}.

Definition chain2Step {P K} {dc2Top: DepsCohs2 P K}
  (s: Chain2Pack dc2Top): Chain2Pack dc2Top :=
  (match s.1 as p0 return
     {k: nat &T {dc2: DepsCohs2 p0 k &T DepsCohs2Chain dc2Top dc2}} ->
     Chain2Pack dc2Top with
   | 0 => fun s' => (0; s')
   | S p' => fun s' => (p'; (s'.1.+1; (proj1DepsCohs2 s'.2.1;
       DepsCohs2ChainCons s'.2.2)))
   end) s.2.

Fixpoint chain2Down {P K} (dc2Top: DepsCohs2 P K) (j: nat):
  Chain2Pack dc2Top :=
  match j with
  | 0 => (P; (K; (dc2Top; DepsCohs2ChainNil)))
  | S j => chain2Step (chain2Down dc2Top j)
  end.

(** The chain images of [Face.v], on packages: the lower one
    ([dc2PackDeps], a [DepsCohsChain] at the same level) and the upper
    one ([dc2PackCohs], one level up through [mkDepsCohs]). *)

Definition DCPack {P K} (dcTop: DepsCohs P K): Type :=
  {p: nat &T {k: nat &T {dc: DepsCohs p k &T DepsCohsChain dcTop dc}}}.

Definition dcStep {P K} {dcTop: DepsCohs P K} (s: DCPack dcTop):
  DCPack dcTop :=
  (match s.1 as p0 return
     {k: nat &T {dc: DepsCohs p0 k &T DepsCohsChain dcTop dc}} ->
     DCPack dcTop with
   | 0 => fun s' => (0; s')
   | S p' => fun s' => (p'; (s'.1.+1; (proj1DepsCohs s'.2.1;
       DepsCohsChainCons s'.2.2)))
   end) s.2.

Definition dc2PackDeps {P K} {T: DepsCohs2 P K} (s: Chain2Pack T):
  DCPack T.(_depsCohs) :=
  (s.1; (s.2.1; (s.2.2.1.(_depsCohs); cohs2ChainDepsCohs s.2.2.2))).

Definition dc2PackCohs {P K} {T: DepsCohs2 P K} (s: Chain2Pack T):
  DCPack (mkDepsCohs T) :=
  (s.1.+1; (s.2.1; (mkDepsCohs s.2.2.1; cohs2ChainCohs s.2.2.2))).

(** The face at the bottom of the relative descent: [νFace] along the
    lower image of the synthesized chain — its result type does not
    depend on the chain's endpoint. Erases dimension [m - j]. *)

Definition νFaceFuel {m} {Xpre: (νSetAt m).(prefix)} (X: νSetFrom m Xpre)
  (j: nat) (ε: arity) (d: νTotal (next X)): νTotal X :=
  νFace ((dc2PackDeps (chain2Down (νDepsCohs2At X) j)).2.2.2) ε d.1.

(** The face maps: relative descent, then [νFaceFuel] *)

Fixpoint gFace {m} {Xpre: (νSetAt m).(prefix)} (X: νSetFrom m Xpre)
  (n: nat) {struct n}:
  forall (dim: nat), dim <= n + m -> arity -> gF0 X n.+1 -> gF0 X n :=
  match n return
    forall (dim: nat), dim <= n + m -> arity -> gF0 X n.+1 -> gF0 X n with
  | 0 => fun dim Hdim ε d => νFaceFuel X (m - dim) ε d
  | S n => fun dim Hdim ε d =>
      gFace (next X) n dim (leR_eq_r (plus_n_Sm n m) Hdim) ε d
  end.

(** The exchange law

    [νFaceCoh] is stated over chains; the synthesized fuels are aligned
    with its chain forms by the package algebra below: packages compose
    ([chain2DownCat]), stages track the fuel ([chain2DownStage]), and —
    the crux — the level-[m.+1] synthesized chain is the [cohs2ChainCohs]
    image of the level-[m] one, for fuels within bound ([packLevelCross],
    resting on [νDepsCohsAt (X.(next)) ≡ mkDepsCohs (νDepsCohs2At X)]). *)

Definition chain2Cat {P K} {T: DepsCohs2 P K} (s1: Chain2Pack T)
  (s2: Chain2Pack s1.2.2.1): Chain2Pack T :=
  (s2.1; (s2.2.1; (s2.2.2.1; cohs2ChainCompose s1.2.2.2 s2.2.2.2))).

Lemma chain2StepStage {P K} {T: DepsCohs2 P K} (s: Chain2Pack T):
  (chain2Step s).1 = Nat.pred s.1.
Proof.
  destruct s as (p, s2). now destruct p.
Qed.

Lemma chain2DownStage {P K} (T: DepsCohs2 P K) (j: nat):
  (chain2Down T j).1 = P - j.
Proof.
  induction j.
  - now rewrite sub0r.
  - now rewrite subSuccR, chain2StepStage, IHj.
Qed.

Lemma dc2PackDepsStep {P K} {T: DepsCohs2 P K} (s: Chain2Pack T):
  dc2PackDeps (chain2Step s) = dcStep (dc2PackDeps s).
Proof.
  destruct s as (p, (k, (dc2, c))). now destruct p.
Qed.

Lemma dc2PackCohsStep {P K} {T: DepsCohs2 P K} (s: Chain2Pack T)
  (p': nat) (e: s.1 = p'.+1):
  dc2PackCohs (chain2Step s) = dcStep (dc2PackCohs s).
Proof.
  destruct s as (p, (k, (dc2, c))). cbn in e. subst p. now reflexivity.
Qed.

Lemma chain2CatStep {P K} {T: DepsCohs2 P K} (s1: Chain2Pack T)
  (s2: Chain2Pack s1.2.2.1):
  chain2Cat s1 (chain2Step s2) = chain2Step (chain2Cat s1 s2).
Proof.
  destruct s2 as (p, (k, (dc2, c))). now destruct p.
Qed.

Lemma chain2DownCat {P K} (T: DepsCohs2 P K) (j1 j2: nat):
  chain2Down T (j2 + j1) =
  chain2Cat (chain2Down T j1) (chain2Down (chain2Down T j1).2.2.1 j2).
Proof.
  induction j2.
  - now reflexivity.
  - cbn. now rewrite IHj2, chain2CatStep.
Qed.

Lemma packLevelCross {m} {Xpre: (νSetAt m).(prefix)} (X: νSetFrom m Xpre)
  (j: nat) (Hj: j <= m):
  dc2PackDeps (chain2Down (νDepsCohs2At (next X)) j) =
  dc2PackCohs (chain2Down (νDepsCohs2At X) j).
Proof.
  revert Hj; induction j; intro Hj.
  - now reflexivity.
  - rewrite dc2PackDepsStep, (IHj (↓ Hj)).
    symmetry.
    now exact (dc2PackCohsStep (chain2Down (νDepsCohs2At X) j) (m - j.+1)
      (chain2DownStage (νDepsCohs2At X) j • subPos Hj)).
Qed.

(** The exchange law at the bottom of the relative descent: after fuel
    arithmetic and package alignment, this is exactly [νFaceCoh]. *)

Lemma νFaceFuelCoh {m} {Xpre: (νSetAt m).(prefix)} (X: νSetFrom m Xpre)
  (q: nat) (Hq: q <= m) (r: nat) (Hr: r <= q) (ε ω: arity)
  (d: νTotal (next (next X))):
  νFaceFuel X (m - q) ε (νFaceFuel (next X) (m.+1 - r) ω d) =
  νFaceFuel X (m - r) ω (νFaceFuel (next X) (m - q) ε d).
Proof.
  unfold νFaceFuel.
  rewrite (subSuccL (Hr ↕ Hq)).
  rewrite (subSplit Hr Hq).
  rewrite (packLevelCross X (m - q) (sub_leR m q)).
  rewrite dc2PackDepsStep.
  rewrite (packLevelCross X ((q - r) + (m - q))
    (leR_eq (subSplit Hr Hq) (sub_leR m r))).
  rewrite (chain2DownCat (νDepsCohs2At X) (m - q) (q - r)).
  now exact (νFaceCoh
    ((chain2Down (νDepsCohs2At X) (m - q)).2.2.2)
    ((chain2Down (chain2Down (νDepsCohs2At X) (m - q)).2.2.1 (q - r)).2.2.2)
    ε ω d.1).
Qed.

(** The relative descent of the exchange law corresponding to [gFace] *)

Fixpoint gFaceCoh {m} {Xpre: (νSetAt m).(prefix)} (X: νSetFrom m Xpre)
  (n: nat) {struct n}:
  forall (q: nat) (Hq: q <= n + m) (r: nat) (Hr: r <= q) (ε ω: arity)
    (d: gF0 X n.+2),
  gFace X n q Hq ε (gFace X n.+1 r (Hr ↕ (↑ Hq)) ω d) =
  gFace X n r (Hr ↕ Hq) ω (gFace X n.+1 q.+1 (⇑ Hq) ε d) :=
  match n return
    forall (q: nat) (Hq: q <= n + m) (r: nat) (Hr: r <= q) (ε ω: arity)
      (d: gF0 X n.+2),
    gFace X n q Hq ε (gFace X n.+1 r (Hr ↕ (↑ Hq)) ω d) =
    gFace X n r (Hr ↕ Hq) ω (gFace X n.+1 q.+1 (⇑ Hq) ε d) with
  | 0 => fun q Hq r Hr ε ω d => νFaceFuelCoh X q Hq r Hr ε ω d
  | S n => fun q Hq r Hr ε ω d =>
      gFaceCoh (next X) n q (leR_eq_r (plus_n_Sm n m) Hq) r Hr ε ω d
  end.

(** The presheaf of a ν-set *)

Definition g (X: νSets): Presheaf := {|
  F0 := gF0 X;
  Face := fun n q Hq ε => gFace X n q (leR_eq_r (plus_n_O n) Hq) ε;
  FaceCoh := fun n q Hq r Hr ε ω d =>
    gFaceCoh X n q (leR_eq_r (plus_n_O n) Hq) r Hr ε ω d;
|}.

End PresheafOfνSet.

Module PresheafOfνSetSimplicial := PresheafOfνSet SimplicialLayer.
Module PresheafOfνSetCubical := PresheafOfνSet CubicalLayer.
