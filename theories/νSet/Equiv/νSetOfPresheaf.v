(** The forward direction of the correspondence between the fibred
    presentation ([Presheaf]) and the indexed construction ([νSet]):
    [f: Presheaf -> νSets].

    The definitions are organized by dependency stage. Each [Psh*] record
    augments the corresponding construction record with presheaf frame maps,
    painting values, or coherence data. The stored carrier level [m] is an
    explicit parameter; SProp bounds relate construction stages to [m], and
    proof irrelevance removes dependence on the bound witnesses. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp Notation νSet.Layer
  νSet Face PresheafEquiv.

From Bonak Require Import Limit.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module νSetOfPresheaf (A: LayerSig).
Import A.

Module Export Face := Face.Face A.
Module Export PshEq := PresheafEquiv.PresheafEquiv A.

Section νSetOfPresheaf.
Variable psh: Presheaf.

(** Presheaf-side lists over the staged dependency construction *)

Fixpoint mkPshFrameTypes (m: nat) {p k}: mkFrameTypes p k -> Type :=
  match p with
  | 0 => fun _ => unit
  | S p => fun frames =>
      { _: mkPshFrameTypes m frames.1 &T psh.(F0) m -> frames.2 }
  end.

Fixpoint mkPshPaintingTypes (m: nat) {p k}:
  forall {frames: mkFrameTypes p k}, mkPshFrameTypes m frames ->
  mkPaintingTypes p k frames -> Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p => fun frames pshFrames paintings =>
      { _: mkPshPaintingTypes m pshFrames.1 paintings.1 &T
        forall d: psh.(F0) m, paintings.2 (pshFrames.2 d) }
  end.

(** The presheaf-side block

    The types of the restr coherences at stages <= p (stating that the
    presheaf-frame maps commute with the face maps and the construction's
    restrictions), together with the next-level presheaf-frame maps they
    determine. The two definitions are mutually dependent, so
    [mkPshRestrTypesAndFrames] constructs them together. *)

Class PshRestrBlock (m: nat) {p k} {frames: mkFrameTypes p k}
  (pshFrames: mkPshFrameTypes m frames) (block: RestrFrameTypeBlock p k) := {
  PshRestrTypesDef: block.(RestrFrameTypesDef) -> Type;
  PshFramesDef: forall {R} (Q: PshRestrTypesDef R),
    mkPshFrameTypes m.+1 (block.(FrameDef) R);
}.

Definition mkPshRestrTypesStep {m p k} {frames: mkFrameTypes p.+1 k}
  (pshFrames: mkPshFrameTypes m frames)
  {prev: RestrFrameTypeBlock p k.+1}
  (prevPsh: PshRestrBlock m pshFrames.1 prev)
  (R: mkRestrFrameTypesStep frames prev): Type :=
  { Q: prevPsh.(PshRestrTypesDef) R.1 &T
    forall q (Hq: q <= k) (Hqp: q + p <= m) (ε: arity) (d: psh.(F0) m.+1),
      pshFrames.2 (psh.(Face) m (q + p) Hqp ε d) =
      R.2 q Hq ε ((prevPsh.(PshFramesDef) Q).2 d) }.

(** The presheaf layer: the level-m painting at the ε-face, transported
    along the diagonal restr coherence *)

Definition mkPshLayer {m p k} {frames: mkFrameTypes p.+1 k}
  {pshFrames: mkPshFrameTypes m frames}
  {paintings: mkPaintingTypes p.+1 k frames}
  (pshPaintings: mkPshPaintingTypes m pshFrames paintings)
  {prev: RestrFrameTypeBlock p k.+1}
  {prevPsh: PshRestrBlock m pshFrames.1 prev}
  {R: mkRestrFrameTypesStep frames prev}
  (Q: mkPshRestrTypesStep pshFrames prevPsh R)
  (Hp: p <= m) (d: psh.(F0) m.+1):
  mkLayer (paintings := paintings) R ((prevPsh.(PshFramesDef) Q.1).2 d) :=
  lam (fun ε =>
    rew [paintings.2] Q.2 0 leR_O Hp ε d in
    pshPaintings.2 (psh.(Face) m p Hp ε d)).

Fixpoint mkPshRestrTypesAndFrames (m: nat) {p k}:
  forall (Hp: p <= m.+1)
    {frames: mkFrameTypes p k} (pshFrames: mkPshFrameTypes m frames)
    {paintings: mkPaintingTypes p k frames}
    (pshPaintings: mkPshPaintingTypes m pshFrames paintings),
  PshRestrBlock m pshFrames (mkRestrFrameTypesAndFrames paintings) :=
  match p return forall (Hp: p <= m.+1)
    (frames: mkFrameTypes p k) (pshFrames: mkPshFrameTypes m frames)
    (paintings: mkPaintingTypes p k frames)
    (pshPaintings: mkPshPaintingTypes m pshFrames paintings),
    PshRestrBlock m pshFrames (mkRestrFrameTypesAndFrames paintings) with
  | 0 => fun Hp frames pshFrames paintings pshPaintings =>
    Build_PshRestrBlock m 0 k frames pshFrames
      (mkRestrFrameTypesAndFrames paintings)
      (fun _ => unit)
      (fun _ _ => (tt; fun _ => tt))
  | S p => fun Hp frames pshFrames paintings pshPaintings =>
    let prevPsh :=
      mkPshRestrTypesAndFrames m (↓ Hp) pshFrames.1 pshPaintings.1 in
    Build_PshRestrBlock m p.+1 k frames pshFrames
      (mkRestrFrameTypesAndFrames paintings)
      (fun R => mkPshRestrTypesStep pshFrames prevPsh R)
      (fun R Q =>
         (prevPsh.(PshFramesDef) Q.1;
          fun d => ((prevPsh.(PshFramesDef) Q.1).2 d;
                    mkPshLayer pshPaintings Q (⇓ Hp) d)))
  end.

(** Presheaf data for [DepsRestr] *)

Class PshDepsRestr (m: nat) (p k: nat) := {
  _pdeps: DepsRestr p k;
  _pshBound: p <= m.+1;
  _pshFrames: mkPshFrameTypes m _pdeps.(_frames);
  _pshPaintings: mkPshPaintingTypes m _pshFrames _pdeps.(_paintings);
  _pshRestrs: (mkPshRestrTypesAndFrames m _pshBound _pshFrames
    _pshPaintings).(PshRestrTypesDef) _pdeps.(_restrFrames);
}.

#[local]
Instance proj1PshDepsRestr {m p k} (P: PshDepsRestr m p.+1 k):
  PshDepsRestr m p k.+1 :=
{|
  _pdeps := P.(_pdeps).(1);
  _pshBound := ↓ P.(_pshBound);
  _pshFrames := P.(_pshFrames).1;
  _pshPaintings := P.(_pshPaintings).1;
  _pshRestrs := P.(_pshRestrs).1;
|}.

Definition mkPshFrames {m p k} (P: PshDepsRestr m p k):
  mkPshFrameTypes m.+1 (mkFrames P.(_pdeps)) :=
  (mkPshRestrTypesAndFrames m P.(_pshBound) P.(_pshFrames)
    P.(_pshPaintings)).(PshFramesDef) P.(_pshRestrs).

Definition mkPshFrame {m p k} (P: PshDepsRestr m p k):
  psh.(F0) m.+1 -> mkFrame P.(_pdeps) := (mkPshFrames P).2.

(** The candidate filler *)

Definition mkPshFiller {m p} (P: PshDepsRestr m p 0):
  mkFrame P.(_pdeps) -> HSet :=
  fun D => {d': psh.(F0) m.+1 & hEq D (mkPshFrame P d')}.

(** Presheaf data for [DepsRestrExtension]

    The top constructor uses the candidate filler definitionally. *)

Inductive PshDepsExtension (m: nat):
  forall {p k} (P: PshDepsRestr m p k),
  DepsRestrExtension p k P.(_pdeps) -> Type :=
| TopPshDep {p} {P: PshDepsRestr m p 0}:
    PshDepsExtension m P (TopRestrDep (mkPshFiller P))
| AddPshDep {p k} (P: PshDepsRestr m p.+1 k)
    {X: DepsRestrExtension p.+1 k P.(_pdeps)}:
    PshDepsExtension m P X ->
    PshDepsExtension m (proj1PshDepsRestr P) (AddRestrDep P.(_pdeps) X).

Arguments TopPshDep {m p P}.
Arguments AddPshDep {m p k} P {X} _.

(** The presheaf painting corresponding to [mkPainting]

    At the top it is [(d; eq_refl)] — the cell
    [d] itself fills its own frame; below, it pairs the layers of the
    presheaf frame one level up. *)

Fixpoint mkPshPainting {m p k} {P: PshDepsRestr m p k}
  {X: DepsRestrExtension p k P.(_pdeps)}
  (PX: PshDepsExtension m P X) (d: psh.(F0) m.+1):
  mkPainting X (mkPshFrame P d) :=
  match PX with
  | TopPshDep => (d; eq_refl)
  | AddPshDep P' PX' => ((mkPshFrame P' d).2; mkPshPainting PX' d)
  end.

Fixpoint mkPshPaintingsPrefix {m p k}:
  forall {P: PshDepsRestr m p k} {X: DepsRestrExtension p k P.(_pdeps)}
  (PX: PshDepsExtension m P X),
  mkPshPaintingTypes m.+1 (mkPshFrames P).1 (mkPaintingsPrefix X) :=
  match p with
  | 0 => fun _ _ _ => tt
  | S p => fun P X PX =>
      (mkPshPaintingsPrefix (AddPshDep P PX); mkPshPainting (AddPshDep P PX))
  end.

Definition mkPshPaintings {m p k} {P: PshDepsRestr m p k}
  {X: DepsRestrExtension p k P.(_pdeps)} (PX: PshDepsExtension m P X):
  mkPshPaintingTypes m.+1 (mkPshFrames P) (mkPaintings X) :=
  (mkPshPaintingsPrefix PX; mkPshPainting PX).

(** Presheaf coherence data for [DepsCohs]

    The remaining presheaf-side data: the coherences stating that the
    presheaf paintings commute with the construction's restr paintings,
    packaged with the construction data they are stated against. From
    these we rebuild everything one level up: the next-level restr
    coherences ([mkPshRestrFrames]) and the next-level restr-painting
    coherences ([mkPshRestrPainting]). *)

(** The face dimension is a [nat] index only; rewriting it under the SProp
    bound needs an equational form. *)

Lemma pshFaceDimIrr {n q q'} (e: q = q') {Hq: q <= n} {Hq': q' <= n}
  (ε: arity) (X: psh.(F0) n.+1):
  psh.(Face) n q Hq ε X = psh.(Face) n q' Hq' ε X.
Proof.
  now destruct e.
Qed.

(** The restr-painting coherence: the top presheaf painting at a face is,
    up to the restr coherence of the frames, the restr painting of the
    presheaf painting one level up (the data corresponding to
    [mkRestrPaintingType]). *)

Definition mkPshRestrPaintingType {m p k} (P: PshDepsRestr m p.+1 k)
  {X: DepsRestrExtension p.+1 k P.(_pdeps)} (PX: PshDepsExtension m P X)
  (restrPaintings: mkRestrPaintingTypes X): Type :=
  forall q (Hq: q <= k) (Hqp: q + p <= m) (ε: arity) (d: psh.(F0) m.+1),
  rew [P.(_pdeps).(_paintings).2] P.(_pshRestrs).2 q Hq Hqp ε d in
    P.(_pshPaintings).2 (psh.(Face) m (q + p) Hqp ε d) =
  restrPaintings.2 q Hq ε (mkPshFrame (proj1PshDepsRestr P) d)
    (mkPshPainting (AddPshDep P PX) d).

Fixpoint mkPshRestrPaintingTypes {m p k}:
  forall (P: PshDepsRestr m p k) {X: DepsRestrExtension p k P.(_pdeps)}
    (PX: PshDepsExtension m P X)
    (restrPaintings: mkRestrPaintingTypes X), Type :=
  match p return forall (P: PshDepsRestr m p k)
    (X: DepsRestrExtension p k P.(_pdeps)) (PX: PshDepsExtension m P X)
    (restrPaintings: mkRestrPaintingTypes X), Type with
  | 0 => fun _ _ _ _ => unit
  | S p => fun P X PX restrPaintings =>
      { _: mkPshRestrPaintingTypes (proj1PshDepsRestr P) (AddPshDep P PX)
             restrPaintings.1 &T
        mkPshRestrPaintingType P PX restrPaintings }
  end.

(** The presheaf-equipped [DepsCohs] *)

Class PshDepsCohs (m p k: nat) := {
  _pshDeps: PshDepsRestr m p k;
  _pExtraDeps: DepsRestrExtension p k _pshDeps.(_pdeps);
  _pshExtraDeps: PshDepsExtension m _pshDeps _pExtraDeps;
  _pRestrPaintings: mkRestrPaintingTypes _pExtraDeps;
  _pshRestrPaintings: mkPshRestrPaintingTypes _pshDeps _pshExtraDeps
    _pRestrPaintings;
  _pCohs: mkCohFrameTypes _pRestrPaintings;
}.

Definition pshDepsCohs {m p k} (PC: PshDepsCohs m p k): DepsCohs p k := {|
  _deps := PC.(_pshDeps).(_pdeps);
  _extraDeps := PC.(_pExtraDeps);
  _restrPaintings := PC.(_pRestrPaintings);
  _cohs := PC.(_pCohs);
|}.

#[local]
Instance proj1PshDepsCohs {m p k} (PC: PshDepsCohs m p.+1 k):
  PshDepsCohs m p k.+1 := {|
  _pshDeps := proj1PshDepsRestr PC.(_pshDeps);
  _pExtraDeps := (PC.(_pshDeps).(_pdeps); PC.(_pExtraDeps))%extradepsrestr;
  _pshExtraDeps := AddPshDep PC.(_pshDeps) PC.(_pshExtraDeps);
  _pRestrPaintings := PC.(_pRestrPaintings).1;
  _pshRestrPaintings := PC.(_pshRestrPaintings).1;
  _pCohs := PC.(_pCohs).1;
|}.

(** The next-level restr coherences to be built (the [_pshRestrs] field of
    the next-level [PshDepsRestr]), and the next-level frame maps *)

Definition mkPshRestrFramesType {m p k} (PC: PshDepsCohs m p k): Type :=
  (mkPshRestrTypesAndFrames m.+1 (⇑ PC.(_pshDeps).(_pshBound))
    (mkPshFrames PC.(_pshDeps))
    (mkPshPaintings PC.(_pshExtraDeps))).(PshRestrTypesDef)
  (mkRestrFrames (depsCohs := pshDepsCohs PC)).

Definition mkPshFramesNext {m p k} (PC: PshDepsCohs m p k)
  (Q: mkPshRestrFramesType PC):
  mkPshFrameTypes m.+2 (mkFrames (mkDepsRestr (depsCohs := pshDepsCohs PC))) :=
  (mkPshRestrTypesAndFrames m.+1 (⇑ PC.(_pshDeps).(_pshBound))
    (mkPshFrames PC.(_pshDeps))
    (mkPshPaintings PC.(_pshExtraDeps))).(PshFramesDef) Q.

(** The next-level restr coherences

    In the layer case ([mkPshRestrLayer]), componentwise equality ([ext])
    reduces the goal to a transport chain. The restr layer of the presheaf
    layer is the presheaf painting at the
    exchanged face pair — [FaceCoh] on the presheaf side matches the stored
    coherence [_pCohs] on the construction side, and the two transport
    chains collapse by [UIP] of the frame ([rew_cohLayer33], as in
    [mkCohLayer]). *)

Lemma mkPshRestrLayer {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  q (Hq: q <= k) (Hqp: q.+1 + p <= m.+1) (ε: arity) (d: psh.(F0) m.+2):
  rew [mkLayer PC.(_pshDeps).(_pdeps).(_restrFrames)]
      (Q.2 q.+1 (⇑ Hq) Hqp ε d) in
    mkPshLayer PC.(_pshDeps).(_pshPaintings) PC.(_pshDeps).(_pshRestrs)
      (⇓ PC.(_pshDeps).(_pshBound)) (psh.(Face) m.+1 (q.+1 + p) Hqp ε d)
  = mkRestrLayer PC.(_pRestrPaintings) PC.(_pCohs) q Hq ε
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).1
      ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).2.
Proof.
  apply ext; intros ω.
  rewrite <- (map_subst (P := mkLayer _) (fun x l => nth l ω)
    (Q.2 q.+1 (⇑ Hq) Hqp ε d)).
  unfold mkPshLayer at 1.
  rewrite nth_lam.
  unfold mkRestrLayer.
  rewrite nth_lmap.
  rewrite nth_lam.
  rewrite <- map_subst with
    (f := fun x => PC.(_pRestrPaintings).2 q Hq ε x).
  rewrite <- (PC.(_pshRestrPaintings).2 q Hq (⇓ Hqp) ε
    (psh.(Face) m.+1 p
      (⇓ (⇑ (proj1PshDepsCohs PC).(_pshDeps).(_pshBound))) ω d)).
  rewrite <- (f_equal_dep _ PC.(_pshDeps).(_pshPaintings).2
    (psh.(FaceCoh) m (q + p) (⇓ Hqp) p (leR_add_l q) ε ω d)).
  eapply (rew_cohLayer33
    (P := fun x => PC.(_pshDeps).(_pdeps).(_paintings).2 x)
    (rf0 := fun x => PC.(_pshDeps).(_pdeps).(_restrFrames).2 0 leR_O ω x)
    (rfF := fun x => PC.(_pshDeps).(_pshFrames).2 x)
    (rfG := fun x => PC.(_pshDeps).(_pdeps).(_restrFrames).2 q Hq ε x)
    (S2 := fun m => PC.(_pshDeps).(_pdeps).(_paintings).2
      (PC.(_pshDeps).(_pshFrames).2 m))
    (S3 := fun n => PC.(_pshDeps).(_pdeps).(_paintings).2
      (PC.(_pshDeps).(_pdeps).(_restrFrames).2 q Hq ε n))
    (F := fun _ a => a) (G := fun _ a => a)).
  now trivial.
  now apply PC.(_pshDeps).(_pdeps).(_frames).2.(UIP).
Qed.

(** The frame case pairs the previous-stage coherence (at a shifted offset:
    the face dimensions [q + p.+1] and [q.+1 + p] are identified by
    [pshFaceDimIrr]) with the layer case. *)

Lemma mkPshRestrFrameStep {m p k} (PC: PshDepsCohs m p.+1 k)
  (Q: mkPshRestrFramesType (proj1PshDepsCohs PC))
  q (Hq: q <= k) (Hqp: q + p.+1 <= m.+1) (ε: arity) (d: psh.(F0) m.+2):
  mkPshFrame PC.(_pshDeps) (psh.(Face) m.+1 (q + p.+1) Hqp ε d) =
  (mkRestrFrames (depsCohs := pshDepsCohs PC)).2 q Hq ε
    ((mkPshFramesNext (proj1PshDepsCohs PC) Q).2 d).
Proof.
  etransitivity.
  - now exact (f_equal (mkPshFrame PC.(_pshDeps))
      (pshFaceDimIrr (eq_sym (plus_n_Sm q p))
        (Hq' := leR_add_shift Hqp) ε d)).
  - now exact (eq_existT_curried
      (Q.2 q.+1 (⇑ Hq) (leR_add_shift Hqp) ε d)
      (mkPshRestrLayer PC Q q Hq (leR_add_shift Hqp) ε d)).
Qed.

Fixpoint mkPshRestrFrames {m p k} (PC: PshDepsCohs m p k) {struct p}:
  mkPshRestrFramesType PC :=
  match p return forall (PC: PshDepsCohs m p k), mkPshRestrFramesType PC with
  | 0 => fun PC => (tt; fun q Hq Hqp ε d => eq_refl)
  | S p => fun PC =>
      (mkPshRestrFrames (proj1PshDepsCohs PC);
       mkPshRestrFrameStep PC (mkPshRestrFrames (proj1PshDepsCohs PC)))
  end PC.

(** The next-level presheaf-equipped [DepsRestr] *)

#[local]
Instance mkPshDepsRestr {m p k} (PC: PshDepsCohs m p k):
  PshDepsRestr m.+1 p.+1 k := {|
  _pdeps := mkDepsRestr (depsCohs := pshDepsCohs PC);
  _pshBound := ⇑ PC.(_pshDeps).(_pshBound);
  _pshFrames := mkPshFrames PC.(_pshDeps);
  _pshPaintings := mkPshPaintings PC.(_pshExtraDeps);
  _pshRestrs := mkPshRestrFrames PC;
|}.

(** Presheaf data for [DepsCohsExtension]

    The top extension is the candidate filler at the next level.
    [mkPshExtraDeps] supplies the presheaf data corresponding to
    [mkExtraDeps]. *)

Inductive PshDepsCohsExtension (m: nat):
  forall {p k} (PC: PshDepsCohs m p k),
  DepsCohsExtension p k (pshDepsCohs PC) -> Type :=
| TopPshCohDep {p} {PC: PshDepsCohs m p 0}:
    PshDepsCohsExtension m PC (TopCohDep (mkPshFiller (mkPshDepsRestr PC)))
| AddPshCohDep {p k} (PC: PshDepsCohs m p.+1 k)
    {XC: DepsCohsExtension p.+1 k (pshDepsCohs PC)}:
    PshDepsCohsExtension m PC XC ->
    PshDepsCohsExtension m (proj1PshDepsCohs PC)
      (AddCohDep (pshDepsCohs PC) XC).

Arguments TopPshCohDep {m p PC}.
Arguments AddPshCohDep {m p k} PC {XC} _.

Fixpoint mkPshExtraDeps {m p k} {PC: PshDepsCohs m p k}
  {XC: DepsCohsExtension p k (pshDepsCohs PC)}
  (PCX: PshDepsCohsExtension m PC XC):
  PshDepsExtension m.+1 (mkPshDepsRestr PC) (mkExtraDeps XC) :=
  match PCX with
  | TopPshCohDep => TopPshDep
  | AddPshCohDep PC' PCX' =>
      AddPshDep (mkPshDepsRestr PC') (mkPshExtraDeps PCX')
  end.

(** The next-level restr-painting coherences

    The definition recurses on the offset [q], following [mkRestrPainting]. At
    [q = 0] both sides are the diagonal layer component; at [q.+1] the pair
    decomposes into the layer case ([mkPshRestrLayer]) and the recursive call
    one stage up. [rew_align] and frame [UIP] identify the transport paths
    across the equality between [q + p.+1] and [q.+1 + p]. *)

Fixpoint mkPshRestrPainting {m p k} {PC: PshDepsCohs m p k}
  {XC: DepsCohsExtension p k (pshDepsCohs PC)}
  (PCX: PshDepsCohsExtension m PC XC) q {struct q}:
  forall (Hq: q <= k) (Hqp: q + p <= m.+1) (ε: arity) (d: psh.(F0) m.+2),
  rew [(mkDepsRestr (depsCohs := pshDepsCohs PC)).(_paintings).2]
      (mkPshRestrFrames PC).2 q Hq Hqp ε d in
    mkPshPainting PC.(_pshExtraDeps) (psh.(Face) m.+1 (q + p) Hqp ε d) =
  (mkRestrPaintings XC).2 q Hq ε
    (mkPshFrame (proj1PshDepsRestr (mkPshDepsRestr PC)) d)
    (mkPshPainting (AddPshDep (mkPshDepsRestr PC) (mkPshExtraDeps PCX)) d).
Proof.
  destruct q; intros.
  - now exact (eq_sym (nth_lam _ ε)).
  - destruct PCX as [| p' k' PC' XC' PCX'].
    + now destruct (leR_O_contra Hq).
    + unshelve eapply (eq_existT_curried_dep
        (Q := mkPainting PC'.(_pExtraDeps))).
      * now exact (mkPshRestrLayer PC'
          (mkPshRestrFrames (proj1PshDepsCohs PC')) q (⇓ Hq) Hqp ε d).
      * etransitivity.
        2: now exact (mkPshRestrPainting m p'.+1 k' PC' XC' PCX' q (⇓ Hq)
             (leR_eq (plus_n_Sm q p') Hqp) ε d).
        apply (rew_align
          (P := fun x => mkPainting PC'.(_pExtraDeps) x)
          (f_equal (mkPshFrame PC'.(_pshDeps))
            (pshFaceDimIrr (plus_n_Sm q p') (Hq := Hqp)
              (Hq' := leR_eq (plus_n_Sm q p') Hqp) ε d))).
        { now exact (eq_trans
            (eq_sym (rew_map
              (fun a => mkPainting PC'.(_pExtraDeps) a)
              (mkPshFrame PC'.(_pshDeps))
              (pshFaceDimIrr (plus_n_Sm q p') (Hq := Hqp)
                (Hq' := leR_eq (plus_n_Sm q p') Hqp) ε d)
              (mkPshPainting PC'.(_pshExtraDeps)
                (psh.(Face) m.+1 (q.+1 + p') Hqp ε d))))
            (f_equal_dep _ (mkPshPainting PC'.(_pshExtraDeps))
              (pshFaceDimIrr (plus_n_Sm q p') (Hq := Hqp)
                (Hq' := leR_eq (plus_n_Sm q p') Hqp) ε d))). }
        now apply (mkFrame PC'.(_pshDeps).(_pdeps)).(UIP).
Defined.

(** The list of next-level restr-painting coherences corresponding to
    [mkRestrPaintingsPrefix]/[mkRestrPaintings] *)

Fixpoint mkPshRestrPaintingsPrefix {m p k}:
  forall {PC: PshDepsCohs m p k}
    {XC: DepsCohsExtension p k (pshDepsCohs PC)}
    (PCX: PshDepsCohsExtension m PC XC),
  mkPshRestrPaintingTypes (proj1PshDepsRestr (mkPshDepsRestr PC))
    (AddPshDep (mkPshDepsRestr PC) (mkPshExtraDeps PCX))
    (mkRestrPaintingsPrefix XC) :=
  match p return forall (PC: PshDepsCohs m p k)
    (XC: DepsCohsExtension p k (pshDepsCohs PC))
    (PCX: PshDepsCohsExtension m PC XC),
    mkPshRestrPaintingTypes (proj1PshDepsRestr (mkPshDepsRestr PC))
      (AddPshDep (mkPshDepsRestr PC) (mkPshExtraDeps PCX))
      (mkRestrPaintingsPrefix XC) with
  | 0 => fun _ _ _ => tt
  | S p => fun PC XC PCX =>
      (mkPshRestrPaintingsPrefix (AddPshCohDep PC PCX);
       mkPshRestrPainting (AddPshCohDep PC PCX))
  end.

Definition mkPshRestrPaintings {m p k} {PC: PshDepsCohs m p k}
  {XC: DepsCohsExtension p k (pshDepsCohs PC)}
  (PCX: PshDepsCohsExtension m PC XC):
  mkPshRestrPaintingTypes (mkPshDepsRestr PC) (mkPshExtraDeps PCX)
    (mkRestrPaintings XC) :=
  (mkPshRestrPaintingsPrefix PCX; mkPshRestrPainting PCX).

(** The face maps on candidate-built cells

    [PshCohsChain] is the presheaf-data counterpart of [DepsCohsChain] one level
    up. It is a chain of [proj1PshDepsCohs] steps, whose image under
    [pshDepsCohs] is a [DepsCohsChain] (definitionally, since [pshDepsCohs]
    commutes with the projections). Along such a chain, the [getFrame]/
    [getPainting] operations of [Face.v] compute on presheaf-built frames and
    paintings ([pshGetFrame], [pshGetPainting]), and [νFace] computes on
    candidate-built frames ([pshνFace]) — the key computation of the [g ∘ f]
    round trip. *)

Inductive PshCohsChain {m P K} (PCTop: PshDepsCohs m P K):
  forall {p k}, PshDepsCohs m p k -> Type :=
| PshCohsChainNil: PshCohsChain PCTop PCTop
| PshCohsChainCons {p k} {PC: PshDepsCohs m p.+1 k}:
    PshCohsChain PCTop PC -> PshCohsChain PCTop (proj1PshDepsCohs PC).

Arguments PshCohsChainNil {m P K PCTop}.
Arguments PshCohsChainCons {m P K PCTop p k PC} _.

Fixpoint pshCohsChainCohs {m P K} {PCTop: PshDepsCohs m P K}
  {p k} {PC: PshDepsCohs m p k} (C: PshCohsChain PCTop PC):
  DepsCohsChain (pshDepsCohs PCTop) (pshDepsCohs PC) :=
  match C with
  | PshCohsChainNil => DepsCohsChainNil
  | PshCohsChainCons C' => DepsCohsChainCons (pshCohsChainCohs C')
  end.

(** Projecting a candidate-built frame down a chain gives the lower-stage
    candidate-built frame — definitionally at each step, since
    [mkPshFrames] builds each stage as a pair over the stage below. *)

Lemma pshGetFrame {m P K} {PCTop: PshDepsCohs m P K}
  {p k} {PC: PshDepsCohs m p k} (C: PshCohsChain PCTop PC)
  (d: psh.(F0) m.+2):
  getFrame (cohsChainNext (pshCohsChainCohs C))
    (mkPshFrame (mkPshDepsRestr PCTop) d) =
  mkPshFrame (mkPshDepsRestr PC) d.
Proof.
  induction C; cbn; [now reflexivity | now rewrite IHC].
Qed.

(** Climbing a presheaf painting rebuilds the top presheaf cell-pair;
    each step holds by conversion. *)

Lemma pshGetPainting {m P K} {PCTop: PshDepsCohs m P K}
  {p k} {PC: PshDepsCohs m p k} (C: PshCohsChain PCTop PC)
  (d: psh.(F0) m.+1):
  getPainting (cohsChainExt (pshCohsChainCohs C))
    (mkPshFrame PC.(_pshDeps) d) (mkPshPainting PC.(_pshExtraDeps) d) =
  (mkPshFrame PCTop.(_pshDeps) d; mkPshPainting PCTop.(_pshExtraDeps) d).
Proof.
  induction C; [now reflexivity | now exact IHC].
Qed.

(** The [ε]-face of a candidate-built cell is the
    candidate-built cell of the [ε]-face — one application of the stored
    restr coherence, cancelled against the layer's transport. *)

Lemma pshνFace {m P K} {PCTop: PshDepsCohs m P K}
  {p k} {PC: PshDepsCohs m p k} (C: PshCohsChain PCTop PC)
  (Hp: p <= m.+1) (ε: arity) (d: psh.(F0) m.+2):
  νFace (pshCohsChainCohs C) ε (mkPshFrame (mkPshDepsRestr PCTop) d) =
  (mkPshFrame PCTop.(_pshDeps) (psh.(Face) m.+1 p Hp ε d);
   mkPshPainting PCTop.(_pshExtraDeps) (psh.(Face) m.+1 p Hp ε d)).
Proof.
  unfold νFace.
  rewrite pshGetFrame.
  rewrite nth_lam.
  refine (f_equal (fun z: {d0: mkFrame PC.(_pshDeps).(_pdeps) &T
      mkPainting PC.(_pExtraDeps) d0} =>
    getPainting (cohsChainExt (pshCohsChainCohs C)) z.1 z.2)
    (eq_existT_curried
      (eq_sym ((mkPshRestrFrames PC).2 0 leR_O Hp ε d))
      (rew_sym_cancel _ _)) • _).
  now exact (pshGetPainting C (psh.(Face) m.+1 p Hp ε d)).
Qed.

(** The tower and the final construction

    [PshTower] stores the presheaf-side data over the dependencies of a
    level-[m.+1] prefix. [PshTowerRestrPaintings] supplies the coherence
    needed by [towerPshDepsCohs], and [towerStep] constructs the state at
    the candidate extension. *)

Definition mkTowerDeps {m} (X: (νSetAt m.+1).(prefix)): DepsRestr m.+1 0 :=
  toDepsRestr ((νSetAt m.+1).(data) X).(restrFrames).

Class PshTower (m: nat) (X: (νSetAt m.+1).(prefix)) := {
  _twFrames: mkPshFrameTypes m (mkTowerDeps X).(_frames);
  _twPaintings: mkPshPaintingTypes m _twFrames (mkTowerDeps X).(_paintings);
  _twRestrs: (mkPshRestrTypesAndFrames m leR_refl _twFrames
    _twPaintings).(PshRestrTypesDef) (mkTowerDeps X).(_restrFrames);
}.

Definition towerPshDeps {m X} (T: PshTower m X): PshDepsRestr m m.+1 0 := {|
  _pdeps := mkTowerDeps X;
  _pshBound := leR_refl;
  _pshFrames := T.(_twFrames);
  _pshPaintings := T.(_twPaintings);
  _pshRestrs := T.(_twRestrs);
|}.

(** The restr-painting coherences at the candidate extension, carried
    alongside the tower state *)

Definition PshTowerRestrPaintings {m X} (T: PshTower m X): Type :=
  mkPshRestrPaintingTypes (towerPshDeps T) TopPshDep
    (((νSetAt m.+1).(data) X).(restrPaintings)
      (mkPshFiller (towerPshDeps T))).

Definition towerPshDepsCohs {m X} (T: PshTower m X)
  (rp: PshTowerRestrPaintings T): PshDepsCohs m m.+1 0 := {|
  _pshDeps := towerPshDeps T;
  _pExtraDeps := TopRestrDep (mkPshFiller (towerPshDeps T));
  _pshExtraDeps := TopPshDep;
  _pRestrPaintings := ((νSetAt m.+1).(data) X).(restrPaintings)
    (mkPshFiller (towerPshDeps T));
  _pshRestrPaintings := rp;
  _pCohs := ((νSetAt m.+1).(data) X).(cohFrames)
    (mkPshFiller (towerPshDeps T));
|}.

(** The level step corresponding to [mkνSetData]: every field is one of the
    rebuilt data above, taken at the candidate extension *)

Definition towerStep {m X} (T: PshTower m X) (rp: PshTowerRestrPaintings T):
  PshTower m.+1 (X; mkPshFiller (towerPshDeps T)) :=
  Build_PshTower m.+1 (X; mkPshFiller (towerPshDeps T))
    (mkPshFrames (towerPshDeps T))
    (mkPshPaintings (TopPshDep (P := towerPshDeps T)))
    (mkPshRestrFrames (towerPshDepsCohs T rp)).

Definition towerStepRestrPaintings {m X} (T: PshTower m X)
  (rp: PshTowerRestrPaintings T):
  PshTowerRestrPaintings (towerStep T rp) :=
  mkPshRestrPaintings (TopPshCohDep (PC := towerPshDepsCohs T rp)).

(** At level 0, the candidate filler pairs a point with an
    identification in the [unit] frame. The level-1 state consists of
    [unit] prefixes and constant frame maps. *)

Definition pshFiller0:
  mkFrame (toDepsRestr ((νSetAt 0).(data) tt).(restrFrames)) -> HSet :=
  fun D => {d': psh.(F0) 0 & hEq D tt}.

Definition tower1: PshTower 0 (tt; pshFiller0).
Proof.
  unshelve esplit.
  - now exact (tt; fun _ => tt).
  - now exact (tt; fun d => (d; eq_refl)).
  - now exact (tt; fun q Hq Hqp ε d => eq_refl).
Defined.

Definition tower1RestrPaintings: PshTowerRestrPaintings tower1.
Proof.
  unshelve esplit.
  - now exact tt.
  - intros q Hq Hqp ε d. destruct q.
    + cbn. now rewrite nth_lam.
    + now destruct (leR_O_contra Hq).
Defined.

(** Closing the tower

    [pshChain] recursively pairs each prefix with the state that produces
    its next extension. Its bonding equations hold by conversion, so
    [this] and [next] of the resulting tower compute to the candidate
    filler and to the tower one level up. *)

Definition PshState (l: nat): (νSetAt l).(prefix) -> Type :=
  match l with
  | 0 => fun _ => unit
  | l.+1 => fun X => {T: PshTower l X &T PshTowerRestrPaintings T}
  end.

Definition pshExtend (l: nat):
  forall (X: (νSetAt l).(prefix)), PshState l X ->
  {E: mkExtensionType X &T PshState l.+1 (X; E)} :=
  match l return forall X: (νSetAt l).(prefix), PshState l X ->
    {E: mkExtensionType X &T PshState l.+1 (X; E)} with
  | 0 => fun X =>
    match X as X0 return PshState 0 X0 ->
      {E: mkExtensionType (X0: (νSetAt 0).(prefix)) &T
       PshState 1 ((X0: (νSetAt 0).(prefix)); E)} with
    | tt => fun _ => (pshFiller0; (tower1; tower1RestrPaintings))
    end
  | l.+1 => fun X s => (mkPshFiller (towerPshDeps s.1);
      (towerStep s.1 s.2; towerStepRestrPaintings s.1 s.2))
  end.

Fixpoint pshChain (l: nat): {X: (νSetAt l).(prefix) &T PshState l X} :=
  match l with
  | 0 => (tt; tt)
  | l.+1 =>
    let s := pshChain l in
    let e := pshExtend l s.1 s.2 in
    ((s.1; e.1); e.2)
  end.

Definition pshApprox (l: nat): (νSetAt l).(prefix) := (pshChain l).1.

Definition pshTw (m: nat): PshTower m (pshApprox m.+1) := (pshChain m.+1).2.1.

Definition pshTwRp (m: nat): PshTowerRestrPaintings (pshTw m) :=
  (pshChain m.+1).2.2.

(** [pshApprox] is definitionally coherent, so its bonding proof is
    reflexivity. *)

Definition pshFrom (n: nat): νSetFrom n (pshApprox n) :=
  ofChain (T := νSetTel) pshApprox (fun _ => eq_refl) n.

Definition f: νSets := pshFrom 0.

End νSetOfPresheaf.

Arguments PshCohsChainNil {psh m P K PCTop}.
Arguments PshCohsChainCons {psh m P K PCTop p k PC} _.

End νSetOfPresheaf.

Module νSetOfPresheafSimplicial := νSetOfPresheaf SimplicialLayer.
Module νSetOfPresheafCubical := νSetOfPresheaf CubicalLayer.
