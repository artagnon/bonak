From Stdlib Require Import Logic.FunctionalExtensionality.
Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeSProp Notation νSet.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Set Typeclasses Depth 10.
Remove Printing Let sigT.
Remove Printing Let prod.

Module νDgnSet (A: νSet.AritySig).
Import A.

Module Import νSet := νSet.νSet A.

Definition FramePrev {p k} (deps: DepsRestr p.+1 k): Type :=
  deps.(_frames).2.

Definition FrameBase {p k} (deps: DepsRestr p.+1 k): Type :=
  mkFrame (deps.(1)).

Definition NextDepsRestr {p k} (depsCohs: DepsCohs p k): DepsRestr p.+1 k :=
  mkDepsRestr.

Fixpoint mkReflFrameTypes {p k}: DepsRestr p k -> Type :=
  match p with
  | 0 => fun _ => unit
  | p'.+1 => fun deps =>
    { R: mkReflFrameTypes deps.(1) &T
          FramePrev deps -> FrameBase deps }
  end.

Class DepsReflRestr p k := {
  _deps: DepsRestr p k;
  _reflFrames: mkReflFrameTypes _deps;
}.

#[local]
Instance proj1DepsRefl {p k}
  `(deps: DepsReflRestr p.+1 k): DepsReflRestr p k.+1 :=
{|
  _deps := proj1DepsRestr (deps.(_deps));
  _reflFrames := deps.(_reflFrames).1;
|}.

Declare Scope depsreflrestr_scope.
Delimit Scope depsreflrestr_scope with depsreflrestr.
Bind Scope depsreflrestr_scope with DepsReflRestr.
Notation "x .(1)" := (proj1DepsRefl x%_depsreflrestr)
  (at level 1, left associativity, format "x .(1)"): depsreflrestr_scope.


Definition ReflFramePrev {p k} (deps: DepsReflRestr p.+1 k): Type :=
  FramePrev deps.(_deps).

Definition ReflFrameBase {p k} (deps: DepsReflRestr p.+1 k): Type :=
  FrameBase deps.(_deps).

Definition restrFrame {p k} i (Hi: i <= k) (deps: DepsRestr p.+1 k) (ε: arity):
  FrameBase deps -> FramePrev deps :=
  deps.(_restrFrames).2 i Hi ε.

Definition reflFrame {p k} (deps: DepsReflRestr p.+1 k):
  ReflFramePrev deps -> ReflFrameBase deps :=
  deps.(_reflFrames).2.

Definition mkIdReflRestrFrameType {p k}
  (deps: DepsReflRestr p.+1 k): Type :=
  forall ε (d: ReflFramePrev deps),
  restrFrame k leR_refl deps.(_deps) ε (reflFrame deps d) = d.

Fixpoint mkIdReflRestrFrameTypes {p}:
  forall {k} (deps: DepsReflRestr p k), Type :=
  match p with
  | 0 => fun _ _ => unit
  | S p =>
    fun k deps =>
    { _: mkIdReflRestrFrameTypes deps.(1) &T
      mkIdReflRestrFrameType deps }
  end.

Definition PaintingPrev {p k} (deps: DepsRestr p.+1 k):
  FramePrev deps -> Type :=
  deps.(_paintings).2.

Definition PaintingBase {p k} (deps: DepsRestr p.+1 k)
  (extraDeps: DepsRestrExtension p.+1 k deps): FrameBase deps -> Type :=
  (mkPaintings (deps; extraDeps)).2.

Definition ReflPaintingPrev {p k} (deps: DepsReflRestr p.+1 k):
  ReflFramePrev deps -> Type :=
  PaintingPrev deps.(_deps).

Definition ReflPaintingBase {p k} (deps: DepsReflRestr p.+1 k)
  (extraDeps: DepsRestrExtension p.+1 k deps.(_deps)):
  ReflFrameBase deps -> Type :=
  PaintingBase deps.(_deps) extraDeps.

Definition mkReflPaintingType {p k} (deps: DepsReflRestr p.+1 k)
  `(extraDeps: DepsRestrExtension p.+1 k deps.(_deps)) :=
  forall (d: ReflFramePrev deps),
  ReflPaintingPrev deps d ->
  ReflPaintingBase deps extraDeps (reflFrame deps d).

Fixpoint mkReflPaintingTypes {p}:
  forall {k} (deps: DepsReflRestr p k)
  `(extraDeps: DepsRestrExtension p k deps.(_deps)), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k deps extraDeps =>
    { _: mkReflPaintingTypes deps.(1) (deps.(_deps); extraDeps) &T
      mkReflPaintingType deps extraDeps }
  end.

Class CohReflRestrFrameTypeBlock {p k} (deps: DepsRestr p k) := {
  CohReflRestrFrameTypesDef: Type;
  ReflFramesDef: CohReflRestrFrameTypesDef -> mkReflFrameTypes deps;
}.

#[local]
Instance toDepsRefl {p k}
  (depsCohs: DepsCohs p k)
  (reflFrames: mkReflFrameTypes depsCohs.(νSet._deps)): DepsReflRestr p k :=
  {| _deps := depsCohs.(νSet._deps);
     _reflFrames := reflFrames;
  |}.

Definition mkCohReflRestrFrameTypesStep {p k} (deps: DepsCohs p.+1 k)
  (reflFrames: mkReflFrameTypes deps.(νSet._deps))
  (prev: CohReflRestrFrameTypeBlock (NextDepsRestr deps.(1))): Type :=
  { Q: prev.(CohReflRestrFrameTypesDef) &T
    forall i (Hi: i <= k) (ε: arity) (d: ReflFrameBase (toDepsRefl deps reflFrames)),
    let reflFrame': FramePrev _ -> FrameBase _ := (prev.(ReflFramesDef) Q).2 in
    reflFrame _ (restrFrame i Hi _ ε d) =
    restrFrame i (↑ Hi) _ ε (reflFrame' d) }.

Definition mkReflLayer {p k} (deps: DepsCohs p.+1 k)
  (reflFrames: mkReflFrameTypes deps.(νSet._deps))
  (reflPaintings: mkReflPaintingTypes (toDepsRefl deps reflFrames)
    deps.(_extraDeps))
  (prev: CohReflRestrFrameTypeBlock (NextDepsRestr deps.(1)))
  (cohFrames: mkCohReflRestrFrameTypesStep deps reflFrames prev)
  (d: ReflFrameBase (toDepsRefl deps reflFrames)):
  mkLayer deps.(νSet._deps).(_restrFrames) d ->
  mkLayer
    (NextDepsRestr deps.(1)).(_restrFrames)
    ((prev.(ReflFramesDef) cohFrames.1).2 d) :=
  fun l ε =>
    rew [(NextDepsRestr deps.(1)).(_paintings).2] cohFrames.2 0 leR_O ε d in
    reflPaintings.2 (restrFrame 0 leR_O (toDepsRefl deps reflFrames).(_deps)
      ε d) (l ε).

Fixpoint mkCohReflRestrFrameTypesAndReflFrames {p k}:
  forall (deps: DepsCohs p k) (reflFrames: mkReflFrameTypes deps.(νSet._deps))
    (reflPaintings: mkReflPaintingTypes (toDepsRefl deps reflFrames)
      deps.(_extraDeps)),
    CohReflRestrFrameTypeBlock (NextDepsRestr deps) :=
  match p with
  | 0 =>
    fun deps reflFrames reflPaintings =>
    {|
      CohReflRestrFrameTypesDef := unit;
      ReflFramesDef _ := (tt; fun _ => tt):
        mkReflFrameTypes (NextDepsRestr deps)
    |}
  | S p =>
    fun deps reflFrames reflPaintings =>
    let prev := mkCohReflRestrFrameTypesAndReflFrames deps.(1)
      reflFrames.1 reflPaintings.1 in
    {|
      CohReflRestrFrameTypesDef := mkCohReflRestrFrameTypesStep deps
        reflFrames prev;
      ReflFramesDef Q :=
        let prevFrames := prev.(ReflFramesDef) Q.1 in
        let reflFrame d := (prevFrames.2 d.1;
          mkReflLayer deps reflFrames reflPaintings prev Q d.1 d.2) in
        (prevFrames; reflFrame): mkReflFrameTypes (NextDepsRestr deps)
    |}
  end.

Definition mkCohReflRestrFrameTypes {p k}
  (deps: DepsCohs p k)
  (reflFrames: mkReflFrameTypes deps.(νSet._deps))
  (reflPaintings: mkReflPaintingTypes (toDepsRefl deps reflFrames)
    deps.(_extraDeps)): Type :=
  (mkCohReflRestrFrameTypesAndReflFrames deps reflFrames
    reflPaintings).(CohReflRestrFrameTypesDef).

Definition mkIdReflRestrPaintingType {p k}
  (deps: DepsCohs p.+1 k)
  (reflFrames: mkReflFrameTypes deps.(νSet._deps))
  (reflPaintings: mkReflPaintingTypes (toDepsRefl deps reflFrames)
    deps.(_extraDeps))
  (idReflRestrFrames: mkIdReflRestrFrameTypes (toDepsRefl deps reflFrames)):
  Type :=
  forall (ε: arity) (d: ReflFramePrev (toDepsRefl deps reflFrames))
    (c: ReflPaintingPrev (toDepsRefl deps reflFrames) d),
  rew [ReflPaintingPrev (toDepsRefl deps reflFrames)] idReflRestrFrames.2 ε d in
  deps.(_restrPaintings).2 k leR_refl ε (reflFrames.2 d) (reflPaintings.2 d c) = c.

Fixpoint mkIdReflRestrPaintingTypes {p}:
  forall {k} (deps: DepsCohs p k)
    (reflFrames: mkReflFrameTypes deps.(νSet._deps))
    (reflPaintings: mkReflPaintingTypes (toDepsRefl deps reflFrames)
      deps.(_extraDeps))
    (idReflRestrFrames: mkIdReflRestrFrameTypes (toDepsRefl deps reflFrames)),
  Type :=
  match p with
  | 0 => fun _ _ _ _ _ => unit
  | S p =>
    fun k deps reflFrames reflPaintings idReflRestrFrames =>
    { _: mkIdReflRestrPaintingTypes deps.(1) reflFrames.1 reflPaintings.1 idReflRestrFrames.1 &T
      mkIdReflRestrPaintingType deps reflFrames reflPaintings
        idReflRestrFrames }
  end.

Class DepsReflCohs p k := {
  _depsCohs2: DepsCohs2 p k;
  _reflFrameDeps: mkReflFrameTypes _depsCohs.(νSet._deps);
  _reflPaintingDeps: mkReflPaintingTypes
    (toDepsRefl _depsCohs _reflFrameDeps) _depsCohs.(_extraDeps);
  _idReflRestrFrames: mkIdReflRestrFrameTypes
    (toDepsRefl _depsCohs _reflFrameDeps);
  _idReflRestrPaintings: mkIdReflRestrPaintingTypes _depsCohs _reflFrameDeps _reflPaintingDeps _idReflRestrFrames;
  _cohReflRestrFrames: mkCohReflRestrFrameTypes _depsCohs _reflFrameDeps _reflPaintingDeps
}.

#[local]
Instance proj1DepsReflCohs {p k} `(depsCohs: DepsReflCohs p.+1 k): DepsReflCohs p k.+1 :=
{|
  _depsCohs2 := (depsCohs.(_depsCohs2)).(1);
  _reflFrameDeps := depsCohs.(_reflFrameDeps).1;
  _reflPaintingDeps := depsCohs.(_reflPaintingDeps).1;
  _idReflRestrFrames := depsCohs.(_idReflRestrFrames).1;
  _idReflRestrPaintings := depsCohs.(_idReflRestrPaintings).1;
  _cohReflRestrFrames := depsCohs.(_cohReflRestrFrames).1;
|}.

Declare Scope depsreflcohs_scope.
Delimit Scope depsreflcohs_scope with depsreflcohs.
Bind Scope depsreflcohs_scope with DepsReflCohs.
Notation "x .(1)" := (proj1DepsReflCohs x%_depsreflcohs)
  (at level 1, left associativity, format "x .(1)"): depsreflcohs_scope.

Definition ReflOfReflCohs {p k}
  `(depsCohs: DepsReflCohs p k): DepsReflRestr p k :=
{|
  _deps := depsCohs.(_depsCohs2).(_depsCohs).(νSet._deps);
  _reflFrames := depsCohs.(_reflFrameDeps);
|}.

Definition RestrOfReflCohs {p k}
  `(depsCohs: DepsReflCohs p k): DepsRestr p k :=
  (ReflOfReflCohs depsCohs).(_deps).

Definition CohsOfReflCohs {p k}
  `(depsCohs: DepsReflCohs p k): DepsCohs p k :=
  depsCohs.(_depsCohs2).(_depsCohs).

Definition RestrExtOfReflCohs {p k}
  `(depsCohs: DepsReflCohs p k): DepsRestrExtension p k
    (RestrOfReflCohs depsCohs) :=
  depsCohs.(_depsCohs2).(_depsCohs).(_extraDeps).

Definition CohsExtOfReflCohs {p k}
  `(depsCohs: DepsReflCohs p k): DepsCohsExtension p k
    (CohsOfReflCohs depsCohs) :=
  depsCohs.(_depsCohs2).(_extraDepsCohs).

Definition mkReflFrames {p k} (deps: DepsReflCohs p k):
  mkReflFrameTypes (NextDepsRestr (CohsOfReflCohs deps)) :=
  (mkCohReflRestrFrameTypesAndReflFrames
    deps.(_depsCohs2).(_depsCohs)
    deps.(_reflFrameDeps)
    deps.(_reflPaintingDeps)).(ReflFramesDef) deps.(_cohReflRestrFrames).

Definition mkReflFrame {p k} (deps: DepsReflCohs p.+1 k):
  FramePrev (NextDepsRestr (CohsOfReflCohs deps)) ->
  FrameBase (NextDepsRestr (CohsOfReflCohs deps)) :=
  (mkReflFrames deps).2.

Definition NextDepsRefl {p k} (deps: DepsReflCohs p k): DepsReflRestr p.+1 k :=
  {| _deps := NextDepsRestr (CohsOfReflCohs deps);
     _reflFrames := mkReflFrames deps
  |}.

Definition restrPainting {p k} (deps: DepsReflCohs p.+1 k):
  forall i (Hi: i <= k) (ε: arity) (d: ReflFrameBase (ReflOfReflCohs deps)),
  ReflPaintingBase (ReflOfReflCohs deps) (RestrExtOfReflCohs deps) d ->
  ReflPaintingPrev (ReflOfReflCohs deps)
    (restrFrame i Hi (RestrOfReflCohs deps) ε d) :=
  deps.(_depsCohs2).(_depsCohs).(_restrPaintings).2.

Definition reflPainting {p k} (deps: DepsReflCohs p.+1 k):
  forall (d: ReflFramePrev (ReflOfReflCohs deps)),
  ReflPaintingPrev (ReflOfReflCohs deps) d ->
  ReflPaintingBase (ReflOfReflCohs deps) (RestrExtOfReflCohs deps)
    (reflFrame (ReflOfReflCohs deps) d) :=
  deps.(_reflPaintingDeps).2.

Definition mkIdReflRestrLayer {p k}
  (deps: DepsReflCohs p.+1 k)
  (ε: arity)
  (d: ReflFrameBase (ReflOfReflCohs deps))
  (l: mkLayer (RestrOfReflCohs deps).(_restrFrames) d)
  (prevIdReflRestrFrames: mkIdReflRestrFrameTypes (NextDepsRefl deps.(1))):
  rew [mkLayer _] prevIdReflRestrFrames.2 ε d in
  mkRestrLayer deps.(_depsCohs2).(_depsCohs).(_restrPaintings)
    (deps.(_depsCohs2).(_depsCohs).(_cohs)) k leR_refl ε _
      (mkReflLayer deps.(_depsCohs2).(_depsCohs)
        ((ReflOfReflCohs deps).(_reflFrames)) deps.(_reflPaintingDeps) _
          deps.(_cohReflRestrFrames) d l) = l.
Proof.
  apply functional_extensionality_dep.
  intros θ.
  unfold mkRestrLayer, mkReflLayer.
  rewrite <- (deps.(_idReflRestrPaintings).2 ε _ (l θ)).
  rewrite <- map_subst_app, <- map_subst.
  unfold reflFrame, restrFrame, toDepsRefl, ReflPaintingPrev, PaintingPrev,
         FramePrev, RestrOfReflCohs, mkFrame; simpl.
  rewrite rew_map with
    (P := fun x => deps.(_depsCohs2).(_depsCohs).(νSet._deps).(_paintings).2 x)
    (f := fun x => (deps.(_depsCohs2).(_depsCohs).(νSet._deps).(_restrFrames).2 0 leR_O θ x)).
  rewrite rew_map with
    (P := fun x => deps.(_depsCohs2).(_depsCohs).(νSet._deps).(_paintings).2 x)
    (f := fun x => ((deps.(_depsCohs2).(_depsCohs).(νSet._deps).(
      _restrFrames).2 k leR_refl ε x))).
  rewrite 2 rew_compose.
  apply rew_swap with (P := fun x =>
    deps.(_depsCohs2).(_depsCohs).(νSet._deps).(_paintings).2 x).
  rewrite rew_app_rl. now trivial.
  now apply (RestrOfReflCohs deps).(_frames).2.(UIP).
Defined.

Fixpoint mkIdReflRestrFrames {p k} (deps: DepsReflCohs p k):
  mkIdReflRestrFrameTypes (NextDepsRefl deps).
  destruct p.
  - simpl. unshelve econstructor. now exact tt. now intros ε [].
  - set (h := mkIdReflRestrFrames p k.+1 deps.(1)%depsreflcohs).
    unshelve econstructor.
    + now apply h.
    + intros ε [l c].
      unshelve eapply eq_existT_curried.
      * now exact (h.2 ε l).
      * now exact (mkIdReflRestrLayer deps ε l c h).
Defined.

Definition mkIdReflRestrFrame {p k} (deps: DepsReflCohs p k):
  mkIdReflRestrFrameType (NextDepsRefl deps) :=
  (mkIdReflRestrFrames deps).2.

Definition HasRefl {p} (deps: DepsReflCohs p 0)
  (E: mkFrame (NextDepsRestr (CohsOfReflCohs deps)) -> HSet): Type :=
  forall (d: FramePrev (NextDepsRestr (CohsOfReflCohs deps)))
    (c: PaintingPrev (NextDepsRestr (CohsOfReflCohs deps)) d),
  let l ε := (rew <- mkIdReflRestrFrame deps ε d in c) in
  E (reflFrame (NextDepsRefl deps) d; l).

Inductive DepsReflCohsExtension p: forall k (deps: DepsReflCohs p k), Type :=
| TopReflCohDep `{deps: DepsReflCohs p 0}
  (L: HasRefl deps (mkPaintings (mkExtraDeps (CohsExtOfReflCohs deps))).2):
  DepsReflCohsExtension p 0 deps
| AddReflCohDep {k} (deps: DepsReflCohs p.+1 k):
  DepsReflCohsExtension p.+1 k deps -> DepsReflCohsExtension p k.+1 deps.(1).

Arguments TopReflCohDep {p deps}.
Arguments AddReflCohDep {p k}.

Declare Scope extra_depsreflcohs_scope.
Delimit Scope extra_depsreflcohs_scope with extradepsreflcohs.
Bind Scope extra_depsreflcohs_scope with DepsReflCohsExtension.
Notation "( x ; y )" := (AddReflCohDep x y)
  (at level 0, format "( x ; y )"): extra_depsreflcohs_scope.


Fixpoint mkReflPainting {p k}
  (deps: DepsReflCohs p k)
  (extraDeps: DepsReflCohsExtension p k deps):
  mkReflPaintingType (NextDepsRefl deps) (mkExtraDeps (CohsExtOfReflCohs deps)).
Proof.
  intros d c.
  destruct extraDeps.
  - unshelve econstructor.
    + intros ε. now exact (rew <- mkIdReflRestrFrame deps ε d in c).
    + now exact (L d c).
  - destruct c as [l c'].
    unshelve econstructor.
    + apply mkReflLayer.
      * now exact (deps.(_reflPaintingDeps)).
      * now exact l.
    + now exact (mkReflPainting p.+1 k deps extraDeps (d; l) c').
Defined.

Fixpoint mkReflPaintingsPrefix {p k}:
  forall (deps: DepsReflCohs p k) (extraDeps: DepsReflCohsExtension p k deps),
  mkReflPaintingTypes
    ((NextDepsRefl deps).(1))
    (NextDepsRestr (CohsOfReflCohs deps);
    mkExtraDeps (CohsExtOfReflCohs deps)) :=
  match p with
  | 0 => fun _ _ => tt
  | S p =>
    fun deps extraDeps =>
      (mkReflPaintingsPrefix deps.(1) (deps; extraDeps);
       mkReflPainting deps.(1) (deps; extraDeps))
  end.

Definition mkReflPaintings {p k}:
  forall (deps: DepsReflCohs p k) (extraDeps: DepsReflCohsExtension p k deps),
  mkReflPaintingTypes (NextDepsRefl deps)
    (mkExtraDeps (CohsExtOfReflCohs deps)) :=
  fun deps extraDeps =>
    (mkReflPaintingsPrefix deps extraDeps; mkReflPainting deps extraDeps).

Definition mkCohReflRestrPaintingType {p k}
  (deps: DepsReflCohs p.+1 k)
  (extraDeps: DepsReflCohsExtension p.+1 k deps): Type :=
  forall (ε: arity) i (Hi: i <= k)
    (d: ReflFrameBase (ReflOfReflCohs deps))
    (c: ReflPaintingBase (ReflOfReflCohs deps) (RestrExtOfReflCohs deps) d),
  rew [ReflPaintingBase
        (toDepsRefl deps.(_depsCohs2).(_depsCohs) deps.(_reflFrameDeps))
        deps.(_depsCohs2).(_depsCohs).(_extraDeps)]
  deps.(_cohReflRestrFrames).2 i Hi ε d in
  deps.(_reflPaintingDeps).2 ((RestrOfReflCohs deps).(_restrFrames).2 i Hi ε d)
    ((CohsOfReflCohs deps).(_restrPaintings).2 i Hi ε d c) =
  mkRestrPainting (CohsExtOfReflCohs deps.(1)) i (↑ Hi) ε (reflFrame (NextDepsRefl deps.(1)) d)
    (mkReflPainting deps.(1) (deps; extraDeps) d c).

Fixpoint mkCohReflRestrPaintingTypes {p}:
  forall {k} (deps: DepsReflCohs p k)
    (extraDeps: DepsReflCohsExtension p k deps), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k deps extraDeps =>
    { _: mkCohReflRestrPaintingTypes deps.(1) (deps; extraDeps)
      &T mkCohReflRestrPaintingType deps extraDeps }
  end.

Fixpoint mkIdReflRestrPainting {p k}
  (deps: DepsReflCohs p k)
  (extraDeps: DepsReflCohsExtension p k deps):
  mkIdReflRestrPaintingType
    (mkDepsCohs deps.(_depsCohs2))
    (mkReflFrames deps)
    (mkReflPaintings deps extraDeps)
    (mkIdReflRestrFrames deps).
Proof.
  intros ε d c.
  destruct extraDeps.
  - destruct deps, _depsCohs3.
    generalize dependent _extraDepsCohs0; intro.
    refine (match _extraDepsCohs0 with TopCohDep E => _ end).
    intros; simpl.
    rewrite rew_compose.
    set (e := (mkIdReflRestrFrames _).2 ε d0).
    enough (eq_sym e • e = eq_refl) as ->. now trivial.
    now apply (mkFrame _).(UIP).
  - unshelve eapply (eq_existT_curried_dep
      (Q := mkPainting deps .(_depsCohs2) .(_depsCohs) .(_extraDeps))).
    * now apply mkIdReflRestrLayer.
    * destruct c as [l c].
      now exact (mkIdReflRestrPainting p.+1 k deps extraDeps ε (d; l) c).
Defined.

Fixpoint mkIdReflRestrPaintings {p k}
  (deps: DepsReflCohs p k)
  (extraDeps: DepsReflCohsExtension p k deps):
  mkIdReflRestrPaintingTypes
    (mkDepsCohs deps.(_depsCohs2))
    (mkReflFrames deps)
    (mkReflPaintings deps extraDeps)
    (mkIdReflRestrFrames deps).
Proof.
  destruct p.
  - unshelve econstructor. now exact tt. now apply mkIdReflRestrPainting.
  - unshelve econstructor.
    + now exact (mkIdReflRestrPaintings p k.+1 deps.(1)%depsreflcohs
      (deps; extraDeps)%extradepsreflcohs).
    + now apply mkIdReflRestrPainting.
Defined.

Class DepsReflCohs2 p k := {
  _depsReflCohs: DepsReflCohs p k;
  _extraDepsCohs2: DepsCohs2Extension p k _depsReflCohs.(_depsCohs2);
  _extraDepsRefl: DepsReflCohsExtension p k _depsReflCohs;
  _cohReflRestrPaintings: mkCohReflRestrPaintingTypes _depsReflCohs _extraDepsRefl;
}.

Definition Cohs2OfReflCohs2 {p k}
  (depsCohs2: DepsReflCohs2 p k): DepsCohs2 p k :=
  depsCohs2.(_depsReflCohs).(_depsCohs2).

Definition ReflOfReflCohs2 {p k}
  `(depsCohs2: DepsReflCohs2 p k): DepsReflRestr p k :=
  ReflOfReflCohs (depsCohs2.(_depsReflCohs)).

Definition RestrOfReflCohs2 {p k}
  `(depsCohs2: DepsReflCohs2 p k): DepsRestr p k :=
  (ReflOfReflCohs (depsCohs2.(_depsReflCohs))).(_deps).

Definition CohsOfReflCohs2 {p k}
  `(depsCohs2: DepsReflCohs2 p k): DepsCohs p k :=
  depsCohs2.(_depsReflCohs).(_depsCohs2).(_depsCohs).

Definition RestrExtOfReflCohs2 {p k}
  `(depsCohs2: DepsReflCohs2 p k): DepsRestrExtension p k
    (RestrOfReflCohs2 depsCohs2) :=
  depsCohs2.(_depsReflCohs).(_depsCohs2).(_depsCohs).(_extraDeps).

Definition CohsExtOfReflCohs2 {p k}
  `(depsCohs2: DepsReflCohs2 p k): DepsCohsExtension p k
    (CohsOfReflCohs2 depsCohs2) :=
  depsCohs2.(_depsReflCohs).(_depsCohs2).(_extraDepsCohs).

#[local]
Instance proj1DepsReflCohs2 {p k} (depsCohs2: DepsReflCohs2 p.+1 k):
DepsReflCohs2 p k.+1 :=
{|
  _depsReflCohs := depsCohs2.(_depsReflCohs).(1);
  _extraDepsCohs2 := (depsCohs2.(_depsReflCohs).(_depsCohs2);
    depsCohs2.(_extraDepsCohs2));
  _extraDepsRefl := (depsCohs2.(_depsReflCohs); depsCohs2.(_extraDepsRefl));
  _cohReflRestrPaintings := depsCohs2.(_cohReflRestrPaintings).1;
|}.

Declare Scope depsreflcohs2_scope.
Delimit Scope depsreflcohs2_scope with depsreflcohs2.
Bind Scope depsreflcohs2_scope with DepsReflCohs2.
Notation "x .(1)" := (proj1DepsReflCohs2 x%depsreflcohs2)
  (at level 1, left associativity, format "x .(1)"): depsreflcohs2_scope.

Definition mkCohReflRestrLayer {p k}
  (deps: DepsReflCohs2 p.+1 k)
  (ε: arity) i (Hi: i <= k)
  (d: mkFrame (((toDepsRefl
    (mkDepsCohs (Cohs2OfReflCohs2 deps))
    (mkReflFrames deps.(_depsReflCohs)))).(_deps).(1).(1)))
  (l: mkLayer (toDepsRefl
    (mkDepsCohs (Cohs2OfReflCohs2 deps))
    (mkReflFrames deps.(_depsReflCohs))).(_deps).(1).(_restrFrames) d)
  (prevCohReflRestrFrames:
    mkCohReflRestrFrameTypes (mkDepsCohs (Cohs2OfReflCohs2 deps).(1))
      (mkReflFrames deps.(_depsReflCohs).(1))
      (mkReflPaintings deps.(_depsReflCohs).(1) (deps.(_depsReflCohs); deps.(_extraDepsRefl)))):
  rew [mkLayer _] prevCohReflRestrFrames.2 i.+1 (⇑ Hi) ε d in
  mkReflLayer
      (CohsOfReflCohs2 deps) deps.(_depsReflCohs).(_reflFrameDeps)
        deps.(_depsReflCohs).(_reflPaintingDeps) _
        deps.(_depsReflCohs).(_cohReflRestrFrames) _
    (mkRestrLayer
      (CohsOfReflCohs2 deps).(_restrPaintings)
      (CohsOfReflCohs2 deps).(_cohs) i Hi ε d l) =
  mkRestrLayer
      (mkDepsCohs (Cohs2OfReflCohs2 deps)).(1).(_restrPaintings)
      (mkDepsCohs (Cohs2OfReflCohs2 deps)).(1).(_cohs) i (↑ Hi) ε _
    (mkReflLayer
      (mkDepsCohs (Cohs2OfReflCohs2 deps).(1))
        (mkReflFrames deps.(_depsReflCohs).(1))
        (mkReflPaintings deps.(_depsReflCohs).(1)
        (deps.(_depsReflCohs); deps.(_extraDepsRefl))) _
        prevCohReflRestrFrames d l).
Proof.
  apply functional_extensionality_dep.
  intros θ.
  unfold mkRestrLayer, mkReflLayer.
  rewrite <- map_subst_app, <- !map_subst.

  set (d0 := restrFrame 0 leR_O (toDepsRefl
    (mkDepsCohs (Cohs2OfReflCohs2 deps).(1))
    (mkReflFrames deps.(_depsReflCohs).(1))).(_deps) θ d).

  assert (h :
    (mkDepsCohs (Cohs2OfReflCohs2 deps)).(1).(_restrPaintings).2 i (↑ Hi) ε
      (reflFrame (toDepsRefl
        (mkDepsCohs (Cohs2OfReflCohs2 deps).(1))
        (mkReflFrames deps.(_depsReflCohs).(1))) d0)
      ((mkReflPaintings deps.(_depsReflCohs).(1)
        (deps.(_depsReflCohs); deps.(_extraDepsRefl))).2 d0 (l θ)) =
    mkRestrPainting (CohsExtOfReflCohs deps.(_depsReflCohs).(1)) i  (↑ Hi) ε
      ((NextDepsRefl deps.(_depsReflCohs).(1)).(_reflFrames).2 d0)
      (mkReflPainting deps.(_depsReflCohs).(1)
         (deps.(_depsReflCohs); deps.(_extraDepsRefl)) d0 (l θ)))
  by reflexivity; rewrite h; clear h.

  rewrite <- (deps.(_cohReflRestrPaintings).2 ε i Hi d0 (l θ)).
  rewrite rew_map with
    (P := fun b => (NextDepsRestr (CohsOfReflCohs2 deps).(1)).(_paintings).2 b)
    (f := fun x => (NextDepsRestr (CohsOfReflCohs2 deps).(1)).(_restrFrames).2
      0 leR_O θ x).
  rewrite rew_map with
    (P := fun rf => ReflPaintingBase _ _ rf)
    (f := fun d0 => reflFrame (toDepsRefl _ _) d0).
  rewrite rew_map with
    (P := fun b => (mkDepsCohs (Cohs2OfReflCohs2 deps)).(1).(
        νSet._deps).(_paintings).2 b)
    (f := fun d0 => (mkDepsCohs (Cohs2OfReflCohs2 deps)).(1).(
      νSet._deps).(_restrFrames).2 i (↑ Hi) ε d0).
  rewrite 4 rew_compose.
  apply rew_swap with
    (P := fun b => (mkDepsCohs (Cohs2OfReflCohs2 deps)).(1).(
      νSet._deps).(_paintings).2 b).
  rewrite rew_app_rl. now trivial.
  now apply (mkFrame (RestrOfReflCohs2 deps).(1)).(UIP).
Defined.

Fixpoint mkCohReflRestrFrames {p k} (deps: DepsReflCohs2 p k):
  mkCohReflRestrFrameTypes
    (mkDepsCohs (Cohs2OfReflCohs2 deps))
    (mkReflFrames deps.(_depsReflCohs))
    (mkReflPaintings deps.(_depsReflCohs) deps.(_extraDepsRefl)).
Proof.
  destruct p.
  - unshelve econstructor. now exact tt. now intros i Hi ε [].
  - set (h := mkCohReflRestrFrames p k.+1 deps.(1)%depsreflcohs2).
    unshelve econstructor.
    + now apply h.
    + intros i Hi ε [l c].
      unshelve eapply eq_existT_curried.
      * now exact (h.2 i.+1 (⇑ Hi) ε l).
      * now exact (mkCohReflRestrLayer deps ε i Hi l c h).
Defined.

Instance mkDepsReflCohs {p k} (deps: DepsReflCohs2 p k): DepsReflCohs p.+1 k.
Proof.
  unshelve econstructor.
  - unshelve econstructor.
    + now exact (mkDepsCohs (Cohs2OfReflCohs2 deps)).
    + now exact (mkExtraCohs deps.(_extraDepsCohs2)).
    + now apply mkCohPaintings.
  - now apply mkReflFrames.
  - now exact (mkReflPaintings _ (deps.(_extraDepsRefl))).
  - now apply mkIdReflRestrFrames.
  - now apply mkIdReflRestrPaintings.
  - now apply mkCohReflRestrFrames.
Defined.

Inductive DepsReflCohs2Extension p: forall k (deps: DepsReflCohs2 p k), Type :=
| TopReflCohDep2 `{deps: DepsReflCohs2 p 0}
  (L: HasRefl
    (mkDepsReflCohs deps)
    (mkPaintings (mkExtraDeps (CohsExtOfReflCohs (mkDepsReflCohs deps)))).2):
  DepsReflCohs2Extension p 0 deps
| AddReflCohDep2 {k} (deps: DepsReflCohs2 p.+1 k):
  DepsReflCohs2Extension p.+1 k deps -> DepsReflCohs2Extension p k.+1 deps.(1)%depsreflcohs2.

Arguments TopReflCohDep2 {p deps}.
Arguments AddReflCohDep2 {p k}.

Declare Scope extra_depsreflcohs2_scope.
Delimit Scope extra_depsreflcohs2_scope with extradepsreflcohs2.
Bind Scope extra_depsreflcohs2_scope with DepsReflCohs2Extension.
Notation "( x ; y )" := (AddReflCohDep2 x y)
  (at level 0, format "( x ; y )"): extra_depsreflcohs2_scope.

Fixpoint mkExtraReflCohs {p k} (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  DepsReflCohsExtension p.+1 k (mkDepsReflCohs deps).
Proof.
  destruct extraDeps.
  - now apply TopReflCohDep.
  - apply (AddReflCohDep (mkDepsReflCohs deps)).
    now exact (mkExtraReflCohs p.+1 k deps extraDeps).
Defined.

Fixpoint mkCohReflRestrPainting {p k}
  (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkCohReflRestrPaintingType (mkDepsReflCohs deps)
    (mkExtraReflCohs deps extraDeps).
Proof.
  intros ε i Hi d [l c].
  destruct i.
  - destruct extraDeps, deps, _depsReflCohs0, _depsCohs3.
    + generalize dependent _extraDepsCohs0; intro.
      refine (match _extraDepsCohs0 with TopCohDep E => _ end).
      now intros.
    + now trivial.
  - unfold ReflPaintingBase, PaintingBase, toDepsRefl; simpl.
    destruct extraDeps.
    + now contradiction.
    + unshelve eapply (eq_existT_curried_dep
        (Q := mkPainting (RestrExtOfReflCohs (mkDepsReflCohs deps.(1))))).
      * now apply (mkCohReflRestrLayer deps ε i (⇓ Hi) d l).
      * now exact (mkCohReflRestrPainting p.+1 k deps extraDeps ε i (⇓ Hi)
          (d; l) c).
Defined.

Fixpoint mkCohReflRestrPaintings {p k}
  (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkCohReflRestrPaintingTypes (mkDepsReflCohs deps)
    (mkExtraReflCohs deps extraDeps).
Proof.
  destruct p.
  - unshelve econstructor. now exact tt. now apply mkCohReflRestrPainting.
  - unshelve econstructor.
    + now exact (mkCohReflRestrPaintings p k.+1 deps.(1)%depsreflcohs2
      (deps; extraDeps)%extradepsreflcohs2).
    + now apply mkCohReflRestrPainting.
Defined.

Definition dgnDepsRestr {p} (C: νSetData p): DepsRestr p 0 :=
  toDepsRestr C.(restrFrames).

Definition dgnDepsRefl {p} (C: νSetData p)
  (reflFrames: mkReflFrameTypes (dgnDepsRestr C)): DepsReflRestr p 0 :=
  {|
    _deps := dgnDepsRestr C;
    _reflFrames := reflFrames;
  |}.

Definition dgnDepsCohs {p} (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet): DepsCohs p 0 :=
  toDepsCohs
    (deps := dgnDepsRestr C)
    (extraDeps := TopRestrDep (deps := dgnDepsRestr C) E)
    (restrPaintings := C.(restrPaintings) E)
    (C.(cohFrames) E).

Definition dgnDepsCohs2 {p} (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet):
  DepsCohs2 p 0 :=
  toDepsCohs2
    (depsCohs := dgnDepsCohs C E)
    (extraDepsCohs := TopCohDep (depsCohs := dgnDepsCohs C E) E')
    (C.(cohPaintings) E E').

Definition dgnDepsReflCohs {p} (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (reflFrames: mkReflFrameTypes (dgnDepsRestr C))
  (reflPaintings: mkReflPaintingTypes
    (dgnDepsRefl C reflFrames)
    (TopRestrDep (deps := dgnDepsRestr C) E))
  (idReflRestrFrames: mkIdReflRestrFrameTypes (dgnDepsRefl C reflFrames))
  (idReflRestrPaintings :
    mkIdReflRestrPaintingTypes (dgnDepsCohs C E)
      reflFrames reflPaintings idReflRestrFrames)
  (cohRestrReflFrames :
    mkCohReflRestrFrameTypes (dgnDepsCohs C E) reflFrames reflPaintings):
  DepsReflCohs p 0 :=
  {|
    _depsCohs2 := dgnDepsCohs2 C E E';
    _reflFrameDeps := reflFrames;
    _reflPaintingDeps := reflPaintings;
    _idReflRestrFrames := idReflRestrFrames;
    _idReflRestrPaintings := idReflRestrPaintings;
    _cohReflRestrFrames := cohRestrReflFrames;
  |}.

Definition dgnHasRefl {p} (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (reflFrames: mkReflFrameTypes (dgnDepsRestr C))
  (reflPaintings :
    mkReflPaintingTypes
      (dgnDepsRefl C reflFrames)
      (TopRestrDep (deps := dgnDepsRestr C) E))
  (idReflRestrFrames: mkIdReflRestrFrameTypes (dgnDepsRefl C reflFrames))
  (idReflRestrPaintings :
    mkIdReflRestrPaintingTypes (dgnDepsCohs C E)
      reflFrames reflPaintings idReflRestrFrames)
  (cohRestrReflFrames :
    mkCohReflRestrFrameTypes (dgnDepsCohs C E)
      reflFrames reflPaintings): Type :=
  HasRefl
    (dgnDepsReflCohs C E E'
      reflFrames reflPaintings
      idReflRestrFrames idReflRestrPaintings
      cohRestrReflFrames)
    (mkPaintings
      (mkExtraDeps
        (CohsExtOfReflCohs
          (dgnDepsReflCohs C E E'
            reflFrames reflPaintings
            idReflRestrFrames idReflRestrPaintings
            cohRestrReflFrames)))).2.

Class DgnData {p} (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet) := {
  reflFrames: mkReflFrameTypes (dgnDepsRestr C);
  reflPaintings :
    mkReflPaintingTypes
      (dgnDepsRefl C reflFrames)
      (TopRestrDep (deps := dgnDepsRestr C) E);
  idReflRestrFrames: mkIdReflRestrFrameTypes (dgnDepsRefl C reflFrames);
  idReflRestrPaintings :
    mkIdReflRestrPaintingTypes
      (dgnDepsCohs C E) reflFrames reflPaintings idReflRestrFrames;
  cohRestrReflFrames (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet):
    mkCohReflRestrFrameTypes (dgnDepsCohs C E) reflFrames reflPaintings;
  cohReflRestrPaintings
    (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
    (L: dgnHasRefl C E E'
      reflFrames reflPaintings
      idReflRestrFrames idReflRestrPaintings
      (cohRestrReflFrames E')):
    mkCohReflRestrPaintingTypes _ (TopReflCohDep L);
}.

Definition dgnDepsReflCohsFromData {p}
  (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (D: DgnData C E): DepsReflCohs p 0 :=
  dgnDepsReflCohs C E E'
    D.(reflFrames) D.(reflPaintings)
    D.(idReflRestrFrames) D.(idReflRestrPaintings)
    (D.(cohRestrReflFrames) E').

Definition dgnHasReflFromData {p}
  (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (D: DgnData C E): Type :=
  dgnHasRefl C E E'
    D.(reflFrames) D.(reflPaintings)
    D.(idReflRestrFrames) D.(idReflRestrPaintings)
    (D.(cohRestrReflFrames) E').

Definition dgnDepsReflCohs2FromData {p}
  (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (E'': mkFrame (dgnDepsRestr (mkνSetData p.+1 (mkνSetData p C E) E')) -> HSet)
  (D: DgnData C E)
  (L: dgnHasReflFromData C E E' D):
  DepsReflCohs2 p 0 :=
  {|
    _depsReflCohs := dgnDepsReflCohsFromData C E E' D;
    _extraDepsCohs2 := TopCoh2Dep (depsCohs2 := dgnDepsCohs2 C E E') E'';
    _extraDepsRefl := TopReflCohDep
      (deps := dgnDepsReflCohsFromData C E E' D) L;
    _cohReflRestrPaintings := D.(cohReflRestrPaintings) E' L;
  |}.

#[local]
Instance mkDgnData {p} (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (D: DgnData C E)
  (L: dgnHasReflFromData C E E' D):
  DgnData (mkνSetData p C E) E' :=
{|
  reflFrames := (mkReflFrames (dgnDepsReflCohsFromData C E E' D):
    mkReflFrameTypes (dgnDepsRestr (mkνSetData p C E)));
  reflPaintings :=
    mkReflPaintings
      (dgnDepsReflCohsFromData C E E' D)
      (TopReflCohDep (deps := dgnDepsReflCohsFromData C E E' D) L);
  idReflRestrFrames := mkIdReflRestrFrames (dgnDepsReflCohsFromData C E E' D);
  idReflRestrPaintings :=
    mkIdReflRestrPaintings
      (dgnDepsReflCohsFromData C E E' D)
      (TopReflCohDep (deps := dgnDepsReflCohsFromData C E E' D) L);
  cohRestrReflFrames := fun E'' =>
    mkCohReflRestrFrames (dgnDepsReflCohs2FromData C E E' E'' D L);
  cohReflRestrPaintings := fun E'' L' =>
    mkCohReflRestrPaintings
      (dgnDepsReflCohs2FromData C E E' E'' D L)
      (TopReflCohDep2 (deps := dgnDepsReflCohs2FromData C E E' E'' D L) L');
|}.

Class νDgnSet p (C: νSet p) := {
  dgnPrefix: (mkνSet C).(prefix) -> Type;
  dgnData (X: (mkνSet C).(prefix)): dgnPrefix X -> DgnData (C.(data) X.1) X.2;
}.

Definition mkDgnPrefix p {C: νSet p} {D: νDgnSet p C}
  (X: (mkνSet (mkνSet C)).(prefix)): Type :=
  { L: D.(dgnPrefix) X.1 &T
    dgnHasReflFromData (C.(data) X.1.1) X.1.2 X.2 (D.(dgnData) X.1 L) }.

#[local]
Definition mkνSetData0: νSetData 0 :=
  {|
    frames := (tt: mkFrameTypes 0 0);
    paintings := (tt: mkPaintingTypes 0 0 (tt: mkFrameTypes 0 0));
    restrFrames :=
      (tt: mkRestrFrameTypes (tt: mkPaintingTypes 0 0 (tt: mkFrameTypes 0 0)));
    restrPaintings := fun _ => tt;
    cohFrames := fun _ => tt;
    cohPaintings := fun _ _ => tt;
  |}.

#[local]
Definition mkDgnData0
  (E: mkFrame (dgnDepsRestr mkνSetData0) -> HSet):
  DgnData mkνSetData0 E :=
  {|
    reflFrames := (tt: mkReflFrameTypes (dgnDepsRestr mkνSetData0));
    reflPaintings := tt;
    idReflRestrFrames := tt;
    idReflRestrPaintings := tt;
    cohRestrReflFrames := fun _ => tt;
    cohReflRestrPaintings := fun _ _ => tt;
  |}.

#[local]
Instance mkνDgnSet0: νDgnSet 0 mkνSet0 :=
  {|
    dgnPrefix := fun _ => unit;
    dgnData := fun (X: (mkνSet mkνSet0).(prefix)) _ =>
      match X.1 as X0 return DgnData (mkνSet0.(data) X0) X.2 with
      | tt => mkDgnData0 X.2
      end;
  |}.

#[local]
Instance mkνDgnSetSn {p} (C: νSet p) (D: νDgnSet p C):
  νDgnSet p.+1 (mkνSet C) :=
  {|
    dgnPrefix := fun X => mkDgnPrefix p (C := C) (D := D) X;
    dgnData := fun X L =>
      mkDgnData (C.(data) X.1.1) X.1.2 X.2 (D.(dgnData) X.1 L.1) L.2;
  |}.

Fixpoint νDgnSetAt n: νDgnSet n (νSetAt n) :=
  match n with
  | O => mkνDgnSet0
  | n.+1 => mkνDgnSetSn (νSetAt n) (νDgnSetAt n)
  end.

CoInductive νDgnSetFrom n
  (X: (νSetAt n).(prefix))
  (M: νSetFrom n X)
  (L: (νDgnSetAt n).(dgnPrefix) (X; this n X M)): Type := dcons {
  dgn: dgnHasReflFromData
    ((νSetAt n).(data) X)
    (this n X M)
    (this n.+1 (X; this n X M) (next n X M))
    ((νDgnSetAt n).(dgnData) (X; this n X M) L);
  dgnNext: νDgnSetFrom n.+1 (X; this n X M) (next n X M) (L; dgn);
}.

Definition νDgnSets (X: νSets) := νDgnSetFrom 0 tt X tt.

End νDgnSet.

Module νDgnSetUnit := νDgnSet νSet.ArityUnit.
Module νDgnSetBool := νDgnSet νSet.ArityBool.

Definition Simplicial := νDgnSetUnit.νDgnSets.
Definition Cubical := νDgnSetBool.νDgnSets.

Example Simplicial1 :=
  Eval lazy in (νDgnSetUnit.νDgnSetAt 1).(νDgnSetUnit.dgnPrefix).

Example Cubical1 :=
  Eval lazy in (νDgnSetBool.νDgnSetAt 1).(νDgnSetBool.dgnPrefix).

Print Simplicial1.
Print Cubical1.
