(** The bisimulation theory of νSets: the staged translation data and the
    coinductive levelwise equivalence [νSetFromEquiv].

    Two towers are bisimilar when their stored frames and paintings
    correspond level by level. That correspondence is carried as data:
    equivalences between the two towers' frames and paintings, from which a
    third instantiation of the block pattern rebuilds the equivalence one
    level up. The frame translations are equivalences *by construction* —
    each stage is a [sigTEquiv]/[layerEquiv] composite of the stage below
    and the stored painting equivalences. The inverse functions and their
    homotopies are supplied by those equivalences.

    Sides: [A] is the target of the translations, [B] the source; frame
    translations go [B -> A] ([eqvFun] of the stored equivalences), and
    so do the painting equivalences, fiberwise over them.
 *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp Notation νSet.Layer νSet.
From Bonak.νSet.Lib Require Import Equiv.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module νSetEquiv (A: LayerSig).
Import A.

Module Export νSet := νSet.νSet A.

(** Lifting equivalences through the layer former

    The layer counterpart of [sigTEquiv]: a layer is a weak product, so
    pointwise equivalences of its components lift to an equivalence of
    layers, with [ext] from the layer interface proving both inverse laws. *)

Definition layerEquiv {B C: arity -> HSet}
  (e: forall ε, Equiv (B ε) (C ε)): Equiv (Layer B) (Layer C).
Proof.
  unshelve refine (qinvEquiv (lmap (fun ε => (e ε).(eqvFun)))
    (lmap (fun ε => invEq (e ε))) _ _).
  - intro l. apply ext; intro ε. rewrite 2 nth_lmap. now apply retEq.
  - intro l. apply ext; intro ε. rewrite 2 nth_lmap. now apply secEq.
Defined.

Lemma layerEquivNth {B C: arity -> HSet} (e: forall ε, Equiv (B ε) (C ε))
  (l: Layer B) (ε: arity): nth (layerEquiv e l) ε = e ε (nth l ε).
Proof.
  now exact (nth_lmap (fun ε => (e ε).(eqvFun)) l ε).
Defined.

(** Equivalence lists over two towers of dependencies *)

Fixpoint mkFrameEqvTypes {p k}:
  mkFrameTypes p k -> mkFrameTypes p k -> Type :=
  match p with
  | 0 => fun _ _ => unit
  | S p => fun framesA framesB =>
      { _: mkFrameEqvTypes framesA.1 framesB.1 &T
        Equiv framesB.2 framesA.2 }
  end.

Fixpoint mkPaintingEqvTypes {p k}:
  forall {framesA framesB: mkFrameTypes p k},
  mkFrameEqvTypes framesA framesB ->
  mkPaintingTypes p k framesA -> mkPaintingTypes p k framesB -> Type :=
  match p with
  | 0 => fun _ _ _ _ _ => unit
  | S p => fun framesA framesB eqvs paintingsA paintingsB =>
      { _: mkPaintingEqvTypes eqvs.1 paintingsA.1 paintingsB.1 &T
        forall d: framesB.2,
          Equiv (paintingsB.2 d) (paintingsA.2 (eqvs.2 d)) }
  end.

(** The translation block

    The types of the translation coherences at stages <= p (the frame
    equivalences commute with the two towers' restrictions), together
    with the next-level frame equivalences they determine. The two
    definitions are mutually dependent, so [mkTrRestrTypesAndFrames]
    constructs them together. *)

Class TrRestrBlock {p k} {framesA framesB: mkFrameTypes p k}
  (eqvs: mkFrameEqvTypes framesA framesB)
  (blockA blockB: RestrFrameTypeBlock p k) := {
  TrRestrTypesDef: blockA.(RestrFrameTypesDef) ->
    blockB.(RestrFrameTypesDef) -> Type;
  FrameEqvDef: forall {RA RB} (Q: TrRestrTypesDef RA RB),
    mkFrameEqvTypes (blockA.(FrameDef) RA) (blockB.(FrameDef) RB);
}.

Definition mkTrRestrTypesStep {p k} {framesA framesB: mkFrameTypes p.+1 k}
  (eqvs: mkFrameEqvTypes framesA framesB)
  {prevA prevB: RestrFrameTypeBlock p k.+1}
  (prevTr: TrRestrBlock eqvs.1 prevA prevB)
  (RA: mkRestrFrameTypesStep framesA prevA)
  (RB: mkRestrFrameTypesStep framesB prevB): Type :=
  { Q: prevTr.(TrRestrTypesDef) RA.1 RB.1 &T
    forall q (Hq: q <= k) (ε: arity) (d: (prevB.(FrameDef) RB.1).2),
      eqvs.2 (RB.2 q Hq ε d) =
      RA.2 q Hq ε ((prevTr.(FrameEqvDef) Q).2 d) }.

(** The layer equivalence: componentwise, the stored painting equivalence
    followed by transport along the diagonal translation coherence *)

Definition mkTrLayerEquiv {p k} {framesA framesB: mkFrameTypes p.+1 k}
  {eqvs: mkFrameEqvTypes framesA framesB}
  {paintingsA: mkPaintingTypes p.+1 k framesA}
  {paintingsB: mkPaintingTypes p.+1 k framesB}
  (pEqvs: mkPaintingEqvTypes eqvs paintingsA paintingsB)
  {prevA prevB: RestrFrameTypeBlock p k.+1}
  {prevTr: TrRestrBlock eqvs.1 prevA prevB}
  {RA: mkRestrFrameTypesStep framesA prevA}
  {RB: mkRestrFrameTypesStep framesB prevB}
  (Q: mkTrRestrTypesStep eqvs prevTr RA RB)
  (d: (prevB.(FrameDef) RB.1).2):
  Equiv (mkLayer (paintings := paintingsB) RB d)
    (mkLayer (paintings := paintingsA) RA
      ((prevTr.(FrameEqvDef) Q.1).2 d)) :=
  layerEquiv (fun ε => compEquiv
    (pEqvs.2 (RB.2 0 leR_O ε d))
    (rewEquiv (fun x => paintingsA.2 x) (Q.2 0 leR_O ε d))).

Fixpoint mkTrRestrTypesAndFrames {p k}:
  forall {framesA framesB: mkFrameTypes p k}
    (eqvs: mkFrameEqvTypes framesA framesB)
    {paintingsA: mkPaintingTypes p k framesA}
    {paintingsB: mkPaintingTypes p k framesB}
    (pEqvs: mkPaintingEqvTypes eqvs paintingsA paintingsB),
  TrRestrBlock eqvs (mkRestrFrameTypesAndFrames paintingsA)
    (mkRestrFrameTypesAndFrames paintingsB) :=
  match p return forall (framesA framesB: mkFrameTypes p k)
    (eqvs: mkFrameEqvTypes framesA framesB)
    (paintingsA: mkPaintingTypes p k framesA)
    (paintingsB: mkPaintingTypes p k framesB)
    (pEqvs: mkPaintingEqvTypes eqvs paintingsA paintingsB),
    TrRestrBlock eqvs (mkRestrFrameTypesAndFrames paintingsA)
      (mkRestrFrameTypesAndFrames paintingsB) with
  | 0 => fun framesA framesB eqvs paintingsA paintingsB pEqvs =>
      Build_TrRestrBlock 0 k framesA framesB eqvs
        (mkRestrFrameTypesAndFrames paintingsA)
        (mkRestrFrameTypesAndFrames paintingsB)
        (fun _ _ => unit)
        (fun _ _ _ => (tt; idEquiv))
  | S p => fun framesA framesB eqvs paintingsA paintingsB pEqvs =>
      let prevTr := mkTrRestrTypesAndFrames eqvs.1 pEqvs.1 in
      Build_TrRestrBlock p.+1 k framesA framesB eqvs
        (mkRestrFrameTypesAndFrames paintingsA)
        (mkRestrFrameTypesAndFrames paintingsB)
        (fun RA RB => mkTrRestrTypesStep eqvs prevTr RA RB)
        (fun RA RB Q =>
          (prevTr.(FrameEqvDef) Q.1;
           sigTEquiv ((prevTr.(FrameEqvDef) Q.1).2)
             (fun d => mkTrLayerEquiv pEqvs Q d)))
  end.

(** The translation-equipped pair of dependencies *)

Class TrDepsRestr (p k: nat) := {
  _depsA: DepsRestr p k;
  _depsB: DepsRestr p k;
  _frameEqvs: mkFrameEqvTypes _depsA.(_frames) _depsB.(_frames);
  _paintingEqvs: mkPaintingEqvTypes _frameEqvs
    _depsA.(_paintings) _depsB.(_paintings);
  _trRestrs: (mkTrRestrTypesAndFrames _frameEqvs
    _paintingEqvs).(TrRestrTypesDef)
    _depsA.(_restrFrames) _depsB.(_restrFrames);
}.

#[local]
Instance proj1TrDepsRestr {p k} (T: TrDepsRestr p.+1 k): TrDepsRestr p k.+1 :=
{|
  _depsA := T.(_depsA).(1);
  _depsB := T.(_depsB).(1);
  _frameEqvs := T.(_frameEqvs).1;
  _paintingEqvs := T.(_paintingEqvs).1;
  _trRestrs := T.(_trRestrs).1;
|}.

(** The computed next-level frame equivalences; their [eqvFun] is the
    frame translation one level up. *)

Definition mkFrameEqvs {p k} (T: TrDepsRestr p k):
  mkFrameEqvTypes (mkFrames T.(_depsA)) (mkFrames T.(_depsB)) :=
  (mkTrRestrTypesAndFrames T.(_frameEqvs)
    T.(_paintingEqvs)).(FrameEqvDef) T.(_trRestrs).

Definition mkFrameEqv {p k} (T: TrDepsRestr p k):
  Equiv (mkFrame T.(_depsB)) (mkFrame T.(_depsA)) := (mkFrameEqvs T).2.

(** The extension layer: relating the two towers' painting extensions

    At the top, an equivalence between the fillers, fiberwise over the
    frame translation. *)

Inductive TrDepsExtension:
  forall {p k} (T: TrDepsRestr p k),
  DepsRestrExtension p k T.(_depsA) ->
  DepsRestrExtension p k T.(_depsB) -> Type :=
| TopTrDep {p} {T: TrDepsRestr p 0}
    {EA: mkFrame T.(_depsA) -> HSet} {EB: mkFrame T.(_depsB) -> HSet}
    (fillerEqvs: forall d: mkFrame T.(_depsB),
      Equiv (EB d) (EA (mkFrameEqv T d))):
    TrDepsExtension T (TopRestrDep EA) (TopRestrDep EB)
| AddTrDep {p k} (T: TrDepsRestr p.+1 k)
    {XA: DepsRestrExtension p.+1 k T.(_depsA)}
    {XB: DepsRestrExtension p.+1 k T.(_depsB)}:
    TrDepsExtension T XA XB ->
    TrDepsExtension (proj1TrDepsRestr T)
      (AddRestrDep T.(_depsA) XA) (AddRestrDep T.(_depsB) XB).

Arguments TopTrDep {p T EA EB} _.
Arguments AddTrDep {p k} T {XA XB} _.

(** The painting equivalences over the frame translation, corresponding to
    [mkPainting]: the filler equivalence at the top, a
    [sigTEquiv]-composite of the layer equivalence and the recursive one
    below. Each case has the constructor structure used by [mkPainting]. *)

Fixpoint mkPaintingEqv {p k} {T: TrDepsRestr p k}
  {XA: DepsRestrExtension p k T.(_depsA)}
  {XB: DepsRestrExtension p k T.(_depsB)}
  (TX: TrDepsExtension T XA XB):
  forall d: mkFrame T.(_depsB),
  Equiv (mkPainting XB d) (mkPainting XA (mkFrameEqv T d)) :=
  match TX with
  | TopTrDep fillerEqvs => fun d => fillerEqvs d
  | AddTrDep T' TX' => fun d =>
      sigTEquiv (mkTrLayerEquiv T'.(_paintingEqvs) T'.(_trRestrs) d)
        (fun l => mkPaintingEqv TX' (d; l))
  end.

Fixpoint mkPaintingEqvsPrefix {p k}:
  forall {T: TrDepsRestr p k}
    {XA: DepsRestrExtension p k T.(_depsA)}
    {XB: DepsRestrExtension p k T.(_depsB)}
    (TX: TrDepsExtension T XA XB),
  mkPaintingEqvTypes (mkFrameEqvs T).1
    (mkPaintingsPrefix XA) (mkPaintingsPrefix XB) :=
  match p with
  | 0 => fun _ _ _ _ => tt
  | S p => fun T XA XB TX =>
      (mkPaintingEqvsPrefix (AddTrDep T TX);
       mkPaintingEqv (AddTrDep T TX))
  end.

Definition mkPaintingEqvs {p k} {T: TrDepsRestr p k}
  {XA: DepsRestrExtension p k T.(_depsA)}
  {XB: DepsRestrExtension p k T.(_depsB)}
  (TX: TrDepsExtension T XA XB):
  mkPaintingEqvTypes (mkFrameEqvs T) (mkPaintings XA) (mkPaintings XB) :=
  (mkPaintingEqvsPrefix TX; mkPaintingEqv TX).

(** Translation coherence data for [DepsCohs]

    The remaining translation data: the coherences stating that the
    painting equivalences commute with the two towers' restr paintings
    ([mkTrRestrPaintingType]), packaged with both sides' construction
    data. From these, everything rebuilds one level
    up — [mkTrRestrFrames] (the next-level translation coherences) and
    [mkTrRestrPainting] (the next-level commutations). *)

Definition mkTrRestrPaintingType {p k} (T: TrDepsRestr p.+1 k)
  {XA: DepsRestrExtension p.+1 k T.(_depsA)}
  {XB: DepsRestrExtension p.+1 k T.(_depsB)}
  (TX: TrDepsExtension T XA XB)
  (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB): Type :=
  forall q (Hq: q <= k) (ε: arity) (d: mkFrame T.(_depsB).(1))
    (c: (mkPaintings (T.(_depsB); XB)).2 d),
  rew [T.(_depsA).(_paintings).2] T.(_trRestrs).2 q Hq ε d in
    T.(_paintingEqvs).2 (T.(_depsB).(_restrFrames).2 q Hq ε d)
      (rpB.2 q Hq ε d c) =
  rpA.2 q Hq ε (mkFrameEqv (proj1TrDepsRestr T) d)
    (mkPaintingEqv (AddTrDep T TX) d c).

Fixpoint mkTrRestrPaintingTypes {p k}:
  forall (T: TrDepsRestr p k)
    {XA: DepsRestrExtension p k T.(_depsA)}
    {XB: DepsRestrExtension p k T.(_depsB)}
    (TX: TrDepsExtension T XA XB)
    (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB), Type :=
  match p return forall (T: TrDepsRestr p k)
    (XA: DepsRestrExtension p k T.(_depsA))
    (XB: DepsRestrExtension p k T.(_depsB))
    (TX: TrDepsExtension T XA XB)
    (rpA: mkRestrPaintingTypes XA) (rpB: mkRestrPaintingTypes XB), Type with
  | 0 => fun _ _ _ _ _ _ => unit
  | S p => fun T XA XB TX rpA rpB =>
      { _: mkTrRestrPaintingTypes (proj1TrDepsRestr T) (AddTrDep T TX)
             rpA.1 rpB.1 &T
        mkTrRestrPaintingType T TX rpA rpB }
  end.

(** The translation-equipped [DepsCohs] pair *)

Class TrDepsCohs (p k: nat) := {
  _trDeps: TrDepsRestr p k;
  _tExtA: DepsRestrExtension p k _trDeps.(_depsA);
  _tExtB: DepsRestrExtension p k _trDeps.(_depsB);
  _trExt: TrDepsExtension _trDeps _tExtA _tExtB;
  _tRpA: mkRestrPaintingTypes _tExtA;
  _tRpB: mkRestrPaintingTypes _tExtB;
  _trRestrPaintings: mkTrRestrPaintingTypes _trDeps _trExt _tRpA _tRpB;
  _tCohsA: mkCohFrameTypes _tRpA;
  _tCohsB: mkCohFrameTypes _tRpB;
}.

Definition trDepsCohsA {p k} (TC: TrDepsCohs p k): DepsCohs p k := {|
  _deps := TC.(_trDeps).(_depsA);
  _extraDeps := TC.(_tExtA);
  _restrPaintings := TC.(_tRpA);
  _cohs := TC.(_tCohsA);
|}.

Definition trDepsCohsB {p k} (TC: TrDepsCohs p k): DepsCohs p k := {|
  _deps := TC.(_trDeps).(_depsB);
  _extraDeps := TC.(_tExtB);
  _restrPaintings := TC.(_tRpB);
  _cohs := TC.(_tCohsB);
|}.

#[local]
Instance proj1TrDepsCohs {p k} (TC: TrDepsCohs p.+1 k): TrDepsCohs p k.+1 :=
{|
  _trDeps := proj1TrDepsRestr TC.(_trDeps);
  _tExtA := (TC.(_trDeps).(_depsA); TC.(_tExtA))%extradepsrestr;
  _tExtB := (TC.(_trDeps).(_depsB); TC.(_tExtB))%extradepsrestr;
  _trExt := AddTrDep TC.(_trDeps) TC.(_trExt);
  _tRpA := TC.(_tRpA).1;
  _tRpB := TC.(_tRpB).1;
  _trRestrPaintings := TC.(_trRestrPaintings).1;
  _tCohsA := TC.(_tCohsA).1;
  _tCohsB := TC.(_tCohsB).1;
|}.

(** The next-level translation coherences to be built, and the
    next-level frame equivalences *)

Definition mkTrRestrFramesType {p k} (TC: TrDepsCohs p k): Type :=
  (mkTrRestrTypesAndFrames (mkFrameEqvs TC.(_trDeps))
    (mkPaintingEqvs TC.(_trExt))).(TrRestrTypesDef)
  (mkRestrFrames (depsCohs := trDepsCohsA TC))
  (mkRestrFrames (depsCohs := trDepsCohsB TC)).

Definition mkTrFrameEqvsNext {p k} (TC: TrDepsCohs p k)
  (Q: mkTrRestrFramesType TC):
  mkFrameEqvTypes (mkFrames (mkDepsRestr (depsCohs := trDepsCohsA TC)))
    (mkFrames (mkDepsRestr (depsCohs := trDepsCohsB TC))) :=
  (mkTrRestrTypesAndFrames (mkFrameEqvs TC.(_trDeps))
    (mkPaintingEqvs TC.(_trExt))).(FrameEqvDef) Q.

Lemma trLayerEqvNth {p k} {framesA framesB: mkFrameTypes p.+1 k}
  {eqvs: mkFrameEqvTypes framesA framesB}
  {paintingsA: mkPaintingTypes p.+1 k framesA}
  {paintingsB: mkPaintingTypes p.+1 k framesB}
  (pEqvs: mkPaintingEqvTypes eqvs paintingsA paintingsB)
  {prevA prevB: RestrFrameTypeBlock p k.+1}
  {prevTr: TrRestrBlock eqvs.1 prevA prevB}
  {RA: mkRestrFrameTypesStep framesA prevA}
  {RB: mkRestrFrameTypesStep framesB prevB}
  (Q: mkTrRestrTypesStep eqvs prevTr RA RB)
  (d: (prevB.(FrameDef) RB.1).2)
  (l: mkLayer (paintings := paintingsB) RB d) (ω: arity):
  nth (mkTrLayerEquiv pEqvs Q d l) ω =
  compEquiv (pEqvs.2 (RB.2 0 leR_O ω d))
    (rewEquiv (fun x => paintingsA.2 x) (Q.2 0 leR_O ω d))
    (nth l ω).
Proof.
  now exact (layerEquivNth _ l ω).
Qed.

(** The next-level translation coherences

    The layer case: componentwise, both sides reduce to transports of the
    translated restricted painting; the stored commutation
    [_trRestrPaintings] identifies them and the two 3-chains collapse by
    [rew_cohLayer33] + [UIP] of the target frame — the [B]-side exchange
    [_tCohsB] entering as a path under the frame equivalence. *)

Lemma mkTrRestrLayer {p k} (TC: TrDepsCohs p.+1 k)
  (Q: mkTrRestrFramesType (proj1TrDepsCohs TC))
  (q: nat) (Hq: q <= k) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := trDepsCohsB (proj1TrDepsCohs TC)))):
  rew [mkLayer TC.(_trDeps).(_depsA).(_restrFrames)]
      (Q.2 q.+1 (⇑ Hq) ε d.1) in
    mkTrLayerEquiv TC.(_trDeps).(_paintingEqvs) TC.(_trDeps).(_trRestrs)
      ((mkRestrFrames
         (depsCohs := trDepsCohsB (proj1TrDepsCohs TC))).2 q.+1 (⇑ Hq) ε d.1)
      (mkRestrLayer TC.(_tRpB) TC.(_tCohsB) q Hq ε d.1 d.2)
  = mkRestrLayer TC.(_tRpA) TC.(_tCohsA) q Hq ε
      ((mkTrFrameEqvsNext (proj1TrDepsCohs TC) Q).2 d).1
      ((mkTrFrameEqvsNext (proj1TrDepsCohs TC) Q).2 d).2.
Proof.
  apply ext; intros ω.
  rewrite <- (map_subst (P := mkLayer _) (fun x l => nth l ω)
    (Q.2 q.+1 (⇑ Hq) ε d.1)).
  rewrite (trLayerEqvNth TC.(_trDeps).(_paintingEqvs)
    TC.(_trDeps).(_trRestrs) _ _ ω).
  change (((mkTrFrameEqvsNext (proj1TrDepsCohs TC) Q).2 d).2) with
    (mkTrLayerEquiv (mkPaintingEqvs (AddTrDep TC.(_trDeps) TC.(_trExt)))
      Q d.1 d.2).
  rewrite 3 nth_lmap.
  cbn [compEquiv rewEquiv eqvFun].
  rewrite <- map_subst with
    (f := fun x => TC.(_trDeps).(_paintingEqvs).2 x).
  rewrite <- map_subst with
    (f := fun x => TC.(_tRpA).2 q Hq ε x).
  rewrite <- (TC.(_trRestrPaintings).2 q Hq ε
    ((mkRestrFrames (depsCohs := trDepsCohsB (proj1TrDepsCohs TC))).2
       0 leR_O ω d.1)
    (nth d.2 ω)).
  eapply (rew_cohLayer33
    (P := fun x => TC.(_trDeps).(_depsA).(_paintings).2 x)
    (rf0 := fun x => TC.(_trDeps).(_depsA).(_restrFrames).2 0 leR_O ω x)
    (rfF := fun x => TC.(_trDeps).(_frameEqvs).2 x)
    (rfG := fun x => TC.(_trDeps).(_depsA).(_restrFrames).2 q Hq ε x)
    (S2 := fun m => TC.(_trDeps).(_depsA).(_paintings).2
      (TC.(_trDeps).(_frameEqvs).2 m))
    (S3 := fun n => TC.(_trDeps).(_depsA).(_paintings).2
      (TC.(_trDeps).(_depsA).(_restrFrames).2 q Hq ε n))
    (F := fun _ a => a) (G := fun _ a => a)).
  now trivial.
  now apply TC.(_trDeps).(_depsA).(_frames).2.(UIP).
Qed.

(** The frame case pairs the previous-stage coherence at offset [q.+1]
    with the layer case: the offsets of the two towers align one to one,
    so the previous-stage coherence applies directly. *)

Lemma mkTrRestrFrameStep {p k} (TC: TrDepsCohs p.+1 k)
  (Q: mkTrRestrFramesType (proj1TrDepsCohs TC))
  (q: nat) (Hq: q <= k) (ε: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := trDepsCohsB (proj1TrDepsCohs TC)))):
  mkFrameEqv TC.(_trDeps)
    ((mkRestrFrames (depsCohs := trDepsCohsB TC)).2 q Hq ε d) =
  (mkRestrFrames (depsCohs := trDepsCohsA TC)).2 q Hq ε
    ((mkTrFrameEqvsNext (proj1TrDepsCohs TC) Q).2 d).
Proof.
  unshelve eapply eq_existT_curried.
  - now exact (Q.2 q.+1 (⇑ Hq) ε d.1).
  - now exact (mkTrRestrLayer TC Q q Hq ε d).
Defined.

Fixpoint mkTrRestrFrames {p k} (TC: TrDepsCohs p k) {struct p}:
  mkTrRestrFramesType TC :=
  match p return forall (TC: TrDepsCohs p k), mkTrRestrFramesType TC with
  | 0 => fun TC => (tt; fun q Hq ε d => eq_refl)
  | S p => fun TC =>
      (mkTrRestrFrames (proj1TrDepsCohs TC);
       mkTrRestrFrameStep TC (mkTrRestrFrames (proj1TrDepsCohs TC)))
  end TC.

(** The next-level translation-equipped pair of dependencies *)

#[local]
Instance mkTrDepsRestr {p k} (TC: TrDepsCohs p k): TrDepsRestr p.+1 k := {|
  _depsA := mkDepsRestr (depsCohs := trDepsCohsA TC);
  _depsB := mkDepsRestr (depsCohs := trDepsCohsB TC);
  _frameEqvs := mkFrameEqvs TC.(_trDeps);
  _paintingEqvs := mkPaintingEqvs TC.(_trExt);
  _trRestrs := mkTrRestrFrames TC;
|}.

(** Translation data for [DepsCohsExtension] one level up *)

Inductive TrDepsCohsExtension:
  forall {p k} (TC: TrDepsCohs p k),
  DepsCohsExtension p k (trDepsCohsA TC) ->
  DepsCohsExtension p k (trDepsCohsB TC) -> Type :=
| TopTrCohDep {p} {TC: TrDepsCohs p 0}
    {EA: mkFrame (mkDepsRestr (depsCohs := trDepsCohsA TC)) -> HSet}
    {EB: mkFrame (mkDepsRestr (depsCohs := trDepsCohsB TC)) -> HSet}
    (fillerEqvs: forall d,
      Equiv (EB d) (EA (mkFrameEqv (mkTrDepsRestr TC) d))):
    TrDepsCohsExtension TC (TopCohDep EA) (TopCohDep EB)
| AddTrCohDep {p k} (TC: TrDepsCohs p.+1 k)
    {XCA: DepsCohsExtension p.+1 k (trDepsCohsA TC)}
    {XCB: DepsCohsExtension p.+1 k (trDepsCohsB TC)}:
    TrDepsCohsExtension TC XCA XCB ->
    TrDepsCohsExtension (proj1TrDepsCohs TC)
      (AddCohDep (trDepsCohsA TC) XCA) (AddCohDep (trDepsCohsB TC) XCB).

Arguments TopTrCohDep {p TC EA EB} _.
Arguments AddTrCohDep {p k} TC {XCA XCB} _.

Fixpoint mkTrExtraDeps {p k} {TC: TrDepsCohs p k}
  {XCA: DepsCohsExtension p k (trDepsCohsA TC)}
  {XCB: DepsCohsExtension p k (trDepsCohsB TC)}
  (TCX: TrDepsCohsExtension TC XCA XCB):
  TrDepsExtension (mkTrDepsRestr TC) (mkExtraDeps XCA) (mkExtraDeps XCB) :=
  match TCX with
  | TopTrCohDep fillerEqvs => TopTrDep fillerEqvs
  | AddTrCohDep TC' TCX' =>
      AddTrDep (mkTrDepsRestr TC') (mkTrExtraDeps TCX')
  end.

(** The next-level restr-painting commutations

    The definition follows [mkRestrPainting] by recursion on the offset [q]. At
    [q = 0] both sides are the diagonal layer component; at [q.+1] the
    pair decomposes into the layer case and the recursive call one stage
    up, with identical transport paths on both sides, so the two match
    directly. *)

Fixpoint mkTrRestrPainting {p k} {TC: TrDepsCohs p k}
  {XCA: DepsCohsExtension p k (trDepsCohsA TC)}
  {XCB: DepsCohsExtension p k (trDepsCohsB TC)}
  (TCX: TrDepsCohsExtension TC XCA XCB) q {struct q}:
  forall (Hq: q <= k) (ε: arity)
    (d: mkFrame (mkDepsRestr (depsCohs := trDepsCohsB TC)).(1))
    (c: (mkPaintings ((mkDepsRestr (depsCohs := trDepsCohsB TC));
           mkExtraDeps XCB)).2 d),
  rew [(mkDepsRestr (depsCohs := trDepsCohsA TC)).(_paintings).2]
      (mkTrRestrFrames TC).2 q Hq ε d in
    mkPaintingEqv TC.(_trExt)
      ((mkDepsRestr (depsCohs := trDepsCohsB TC)).(_restrFrames).2 q Hq ε d)
      ((mkRestrPaintings XCB).2 q Hq ε d c) =
  (mkRestrPaintings XCA).2 q Hq ε
    (mkFrameEqv (proj1TrDepsRestr (mkTrDepsRestr TC)) d)
    (mkPaintingEqv (AddTrDep (mkTrDepsRestr TC) (mkTrExtraDeps TCX)) d c).
Proof.
  destruct q; intros.
  - now exact (eq_sym
      (trLayerEqvNth (mkPaintingEqvs TC.(_trExt)) (mkTrRestrFrames TC)
        d c.1 ε)).
  - destruct TCX as [| p' k' TC' XCA' XCB' TCX'].
    + now destruct (leR_O_contra Hq).
    + unshelve eapply (eq_existT_curried_dep
        (Q := mkPainting TC'.(_tExtA))).
      * now exact (mkTrRestrLayer TC'
          (mkTrRestrFrames (proj1TrDepsCohs TC')) q (⇓ Hq) ε (d; c.1)).
      * now exact (mkTrRestrPainting p'.+1 k' TC' XCA' XCB' TCX' q (⇓ Hq) ε
          (d; c.1) c.2).
Defined.

Fixpoint mkTrRestrPaintingsPrefix {p k}:
  forall {TC: TrDepsCohs p k}
    {XCA: DepsCohsExtension p k (trDepsCohsA TC)}
    {XCB: DepsCohsExtension p k (trDepsCohsB TC)}
    (TCX: TrDepsCohsExtension TC XCA XCB),
  mkTrRestrPaintingTypes (proj1TrDepsRestr (mkTrDepsRestr TC))
    (AddTrDep (mkTrDepsRestr TC) (mkTrExtraDeps TCX))
    (mkRestrPaintingsPrefix XCA) (mkRestrPaintingsPrefix XCB) :=
  match p return forall (TC: TrDepsCohs p k)
    (XCA: DepsCohsExtension p k (trDepsCohsA TC))
    (XCB: DepsCohsExtension p k (trDepsCohsB TC))
    (TCX: TrDepsCohsExtension TC XCA XCB),
    mkTrRestrPaintingTypes (proj1TrDepsRestr (mkTrDepsRestr TC))
      (AddTrDep (mkTrDepsRestr TC) (mkTrExtraDeps TCX))
      (mkRestrPaintingsPrefix XCA) (mkRestrPaintingsPrefix XCB) with
  | 0 => fun _ _ _ _ => tt
  | S p => fun TC XCA XCB TCX =>
      (mkTrRestrPaintingsPrefix (AddTrCohDep TC TCX);
       mkTrRestrPainting (AddTrCohDep TC TCX))
  end.

Definition mkTrRestrPaintings {p k} {TC: TrDepsCohs p k}
  {XCA: DepsCohsExtension p k (trDepsCohsA TC)}
  {XCB: DepsCohsExtension p k (trDepsCohsB TC)}
  (TCX: TrDepsCohsExtension TC XCA XCB):
  mkTrRestrPaintingTypes (mkTrDepsRestr TC) (mkTrExtraDeps TCX)
    (mkRestrPaintings XCA) (mkRestrPaintings XCB) :=
  (mkTrRestrPaintingsPrefix TCX; mkTrRestrPainting TCX).

(** The tower data at a coinductive position *)

Definition νDataAt {m} (Xpre: (νSetAt m).(prefix)): νSetData m :=
  (νSetAt m).(data) Xpre.

(** The bisimulation tower and the coinductive equivalence

    The corecursive state at a tower level: the translation data over
    the two [νSetAt]-towers'
    dependencies at a pair of prefixes, with the assembled [TrDepsRestr]
    pinned by construction. The coinductive [νSetFromEquiv] then carries,
    at each level, the filler equivalence, the restr-painting
    commutations at it, and corecursively the equivalence of the tails
    over the stepped state. *)

Definition νTowerDeps {n} (Xpre: (νSetAt n).(prefix)): DepsRestr n 0 :=
  toDepsRestr (νDataAt Xpre).(restrFrames).

Class TrTower (n: nat) (XpreA XpreB: (νSetAt n).(prefix)) := {
  _twFrameEqvs: mkFrameEqvTypes (νTowerDeps XpreA).(_frames)
    (νTowerDeps XpreB).(_frames);
  _twPaintingEqvs: mkPaintingEqvTypes _twFrameEqvs
    (νTowerDeps XpreA).(_paintings) (νTowerDeps XpreB).(_paintings);
  _twTrRestrs: (mkTrRestrTypesAndFrames _twFrameEqvs
    _twPaintingEqvs).(TrRestrTypesDef)
    (νTowerDeps XpreA).(_restrFrames) (νTowerDeps XpreB).(_restrFrames);
}.

Definition towerTrDeps {n} {XpreA XpreB: (νSetAt n).(prefix)}
  (W: TrTower n XpreA XpreB): TrDepsRestr n 0 := {|
  _depsA := νTowerDeps XpreA;
  _depsB := νTowerDeps XpreB;
  _frameEqvs := W.(_twFrameEqvs);
  _paintingEqvs := W.(_twPaintingEqvs);
  _trRestrs := W.(_twTrRestrs);
|}.

Definition trTowerDepsCohs {n} {XpreA XpreB: (νSetAt n).(prefix)}
  (W: TrTower n XpreA XpreB)
  {EA: mkFrame (νTowerDeps XpreA) -> HSet}
  {EB: mkFrame (νTowerDeps XpreB) -> HSet}
  (fEqv: forall d, Equiv (EB d) (EA (mkFrameEqv (towerTrDeps W) d)))
  (rp: mkTrRestrPaintingTypes (towerTrDeps W)
    (TopTrDep (T := towerTrDeps W) fEqv)
    ((νDataAt XpreA).(restrPaintings) EA)
    ((νDataAt XpreB).(restrPaintings) EB)):
  TrDepsCohs n 0 := {|
  _trDeps := towerTrDeps W;
  _tExtA := TopRestrDep EA;
  _tExtB := TopRestrDep EB;
  _trExt := TopTrDep (T := towerTrDeps W) fEqv;
  _tRpA := (νDataAt XpreA).(restrPaintings) EA;
  _tRpB := (νDataAt XpreB).(restrPaintings) EB;
  _trRestrPaintings := rp;
  _tCohsA := (νDataAt XpreA).(cohFrames) EA;
  _tCohsB := (νDataAt XpreB).(cohFrames) EB;
|}.

Definition trTowerStep {n} {XpreA XpreB: (νSetAt n).(prefix)}
  (W: TrTower n XpreA XpreB)
  {EA: mkFrame (νTowerDeps XpreA) -> HSet}
  {EB: mkFrame (νTowerDeps XpreB) -> HSet}
  (fEqv: forall d, Equiv (EB d) (EA (mkFrameEqv (towerTrDeps W) d)))
  (rp: mkTrRestrPaintingTypes (towerTrDeps W)
    (TopTrDep (T := towerTrDeps W) fEqv)
    ((νDataAt XpreA).(restrPaintings) EA)
    ((νDataAt XpreB).(restrPaintings) EB)):
  TrTower n.+1 (XpreA; EA) (XpreB; EB) :=
  Build_TrTower n.+1 (XpreA; EA) (XpreB; EB)
    (mkFrameEqvs (towerTrDeps W))
    (mkPaintingEqvs (TopTrDep (T := towerTrDeps W) fEqv))
    (mkTrRestrFrames (trTowerDepsCohs W fEqv rp)).

CoInductive νSetFromEquiv {n} {XpreA XpreB: (νSetAt n).(prefix)}
  (W: TrTower n XpreA XpreB)
  (SA: νSetFrom n XpreA) (SB: νSetFrom n XpreB): Type := trCons {
  thisEquiv: forall d: mkFrame (νTowerDeps XpreB),
    Equiv (SB.(this _ _) d)
      (SA.(this _ _) (mkFrameEqv (towerTrDeps W) d));
  trRpEquiv: mkTrRestrPaintingTypes (towerTrDeps W)
    (TopTrDep (T := towerTrDeps W) thisEquiv)
    ((νDataAt XpreA).(restrPaintings) (SA.(this _ _)))
    ((νDataAt XpreB).(restrPaintings) (SB.(this _ _)));
  nextEquiv: νSetFromEquiv (trTowerStep W thisEquiv trRpEquiv)
    (SA.(next _ _)) (SB.(next _ _));
}.

Definition trTower0: TrTower 0 tt tt := Build_TrTower 0 tt tt tt tt tt.

End νSetEquiv.

Module νSetEquivSimplicial := νSetEquiv SimplicialLayer.
Module νSetEquivCubical := νSetEquiv CubicalLayer.
