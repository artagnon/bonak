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
Arguments mkDepsRestr {p k} depsCohs.

Definition FramePrev {p k} (deps: DepsRestr p.+1 k): Type :=
  deps.(_frames).2.

Definition FrameBase {p k} (deps: DepsRestr p.+1 k): Type :=
  mkFrame (deps.(1)).

Definition PaintingPrev {p k} (deps: DepsRestr p.+1 k):
  FramePrev deps -> Type :=
  deps.(_paintings).2.

Definition PaintingBase {p k} (deps: DepsRestr p.+1 k)
  (extraDeps: DepsRestrExtension p.+1 k deps): FrameBase deps -> Type :=
  (mkPaintings (deps; extraDeps)).2.

Fixpoint mkReflFrameBelowTypes {p k}: DepsRestr p k -> Type :=
  match p with
  | 0 => fun _ => unit
  | p'.+1 => fun deps =>
    { R: mkReflFrameBelowTypes deps.(1) &T
          forall i (Hi: i <= k), FramePrev deps -> FrameBase deps }
  end.

Fixpoint mkReflFrameAboveTypes {p k}: DepsRestr p k -> Type :=
  match p with
  | 0 => fun _ => unit
  | p'.+1 => fun deps =>
    { R: mkReflFrameAboveTypes deps.(1) &T
          forall i (Hi: i <= p') (d: FramePrev deps), PaintingPrev deps d -> mkFrame deps }
  end.

Class DepsReflBelow p k := {
  _depsRestr: DepsRestr p k;
  _reflFramesBelow: mkReflFrameBelowTypes _depsRestr;
}.

#[local]
Instance proj1DepsReflBelow {p k}
  (deps: DepsReflBelow p.+1 k): DepsReflBelow p k.+1 :=
{|
  _depsRestr := proj1DepsRestr (deps.(_depsRestr));
  _reflFramesBelow := deps.(_reflFramesBelow).1;
|}.

Declare Scope depsreflbelow_scope.
Delimit Scope depsreflbelow_scope with depsreflbelow.
Bind Scope depsreflbelow_scope with DepsReflBelow.
Notation "x .(1)" := (proj1DepsReflBelow x%depsreflbelow)
  (at level 1, left associativity, format "x .(1)"): depsreflbelow_scope.

Definition mkIdReflRestrFrameBelowType {p k}
  (deps: DepsReflBelow p.+1 k): Type :=
  forall i (Hi: i <= k) ε (d: FramePrev deps.(_depsRestr)),
  deps.(_depsRestr).(_restrFrames).2 i Hi ε (deps.(_reflFramesBelow).2 i Hi d) = d.

Fixpoint mkIdReflRestrFrameBelowTypes {p}:
  forall {k} (deps: DepsReflBelow p k), Type :=
  match p with
  | 0 => fun _ _ => unit
  | S p =>
    fun k deps =>
    { _: mkIdReflRestrFrameBelowTypes deps.(1) &T
      mkIdReflRestrFrameBelowType deps }
  end.

Definition mkReflPaintingBelowType {p k} (deps: DepsReflBelow p.+1 k)
  (extraDeps: DepsRestrExtension p.+1 k deps.(_depsRestr)) :=
  forall i (Hi: i <= k) (d: FramePrev deps.(_depsRestr)),
  PaintingPrev deps.(_depsRestr) d ->
  PaintingBase deps.(_depsRestr) extraDeps (deps.(_reflFramesBelow).2 i Hi d).

Fixpoint mkReflPaintingBelowTypes {p}:
  forall {k} (deps: DepsReflBelow p k)
  (extraDeps: DepsRestrExtension p k deps.(_depsRestr)), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k deps extraDeps =>
    { _: mkReflPaintingBelowTypes deps.(1) (deps.(_depsRestr); extraDeps) &T
      mkReflPaintingBelowType deps extraDeps }
  end.

Class CohReflRestrFrameBelowInfTypeBlock {p k} (deps: DepsRestr p k) := {
  CohReflRestrFrameBelowInfTypesDef: Type;
  ReflFramesBelowDef: CohReflRestrFrameBelowInfTypesDef -> mkReflFrameBelowTypes deps;
}.

#[local]
Instance toDepsReflBelow {p k}
  (depsCohs: DepsCohs p k)
  (reflFrames: mkReflFrameBelowTypes depsCohs.(_deps)): DepsReflBelow p k :=
  {| _depsRestr := depsCohs.(_deps);
     _reflFramesBelow := reflFrames;
  |}.

Definition mkCohReflRestrFrameBelowInfTypesStep {p k} (deps: DepsCohs p.+1 k)
  (reflFramesBelow: mkReflFrameBelowTypes deps.(_deps))
  (prev: CohReflRestrFrameBelowInfTypeBlock (mkDepsRestr deps.(1))): Type :=
  { Q: prev.(CohReflRestrFrameBelowInfTypesDef) &T
    forall q r (Hq: q <= k) (Hr: r <= q) (ε: arity) (d: FrameBase deps.(_deps)),
    reflFramesBelow.2 q Hq (deps.(_deps).(_restrFrames).2 r (Hr ↕ Hq) ε d) =
    mkRestrFrame r (Hr ↕ ↑ Hq) ε ((prev.(ReflFramesBelowDef) Q).2 q.+1 (⇑ Hq) d) }.

Definition mkReflLayerBelow {p k} (deps: DepsCohs p.+1 k)
  (reflFramesBelow: mkReflFrameBelowTypes deps.(_deps))
  (reflPaintingsBelow: mkReflPaintingBelowTypes (toDepsReflBelow deps reflFramesBelow)
    deps.(_extraDeps))
  (prev: CohReflRestrFrameBelowInfTypeBlock (mkDepsRestr deps.(1)))
  (cohFrames: mkCohReflRestrFrameBelowInfTypesStep deps reflFramesBelow prev)
  i (Hi: i <= k)
  (d: FrameBase deps.(_deps)):
  mkLayer deps.(_deps).(_restrFrames) d ->
  mkLayer
    (mkDepsRestr deps.(1)).(_restrFrames)
    ((prev.(ReflFramesBelowDef) cohFrames.1).2 i.+1 (⇑ Hi) d) :=
  fun l ε =>
    rew [(mkDepsRestr deps.(1)).(_paintings).2]
      cohFrames.2 i 0 Hi leR_O ε d in
    reflPaintingsBelow.2 i Hi (deps.(_deps).(_restrFrames).2 0 leR_O ε d) (l ε).

Fixpoint mkCohReflRestrFrameBelowInfTypesAndReflFramesBelow {p k}:
  forall (deps: DepsCohs p k) (reflFramesBelow: mkReflFrameBelowTypes deps.(_deps))
    (reflPaintingsBelow: mkReflPaintingBelowTypes (toDepsReflBelow deps reflFramesBelow)
      deps.(_extraDeps)),
    CohReflRestrFrameBelowInfTypeBlock (mkDepsRestr deps) :=
  match p with
  | 0 =>
    fun deps reflFrames reflPaintings =>
    {|
      CohReflRestrFrameBelowInfTypesDef := unit;
      ReflFramesBelowDef _ :=
        let reflFrame0: forall i (Hi: i <= k),
          FramePrev (mkDepsRestr deps) -> FrameBase (mkDepsRestr deps) :=
          fun _ _ d => d in
        (((tt: mkReflFrameBelowTypes (mkDepsRestr deps).(1)); reflFrame0):
          mkReflFrameBelowTypes (mkDepsRestr deps))
    |}
  | S p =>
    fun deps reflFramesBelow reflPaintingsBelow =>
    let prev := mkCohReflRestrFrameBelowInfTypesAndReflFramesBelow deps.(1)
      reflFramesBelow.1 reflPaintingsBelow.1 in
    {|
      CohReflRestrFrameBelowInfTypesDef := mkCohReflRestrFrameBelowInfTypesStep deps
        reflFramesBelow prev;
      ReflFramesBelowDef Q :=
        let prevFrames := prev.(ReflFramesBelowDef) Q.1 in
        let reflFrame i (Hi: i <= k) d := (prevFrames.2 i.+1 (⇑ Hi) d.1;
          mkReflLayerBelow deps reflFramesBelow reflPaintingsBelow prev Q i Hi d.1 d.2) in
        (prevFrames; reflFrame): mkReflFrameBelowTypes (mkDepsRestr deps)
    |}
  end.

Definition mkCohReflRestrFrameBelowInfTypes {p k}
  (deps: DepsCohs p k)
  (reflFramesBelow: mkReflFrameBelowTypes deps.(_deps))
  (reflPaintingsBelow: mkReflPaintingBelowTypes (toDepsReflBelow deps reflFramesBelow)
    deps.(_extraDeps)): Type :=
  (mkCohReflRestrFrameBelowInfTypesAndReflFramesBelow deps reflFramesBelow
    reflPaintingsBelow).(CohReflRestrFrameBelowInfTypesDef).

Definition mkIdReflRestrPaintingBelowType {p k}
  (deps: DepsCohs p.+1 k)
  (reflFramesBelow: mkReflFrameBelowTypes deps.(_deps))
  (reflPaintingsBelow: mkReflPaintingBelowTypes (toDepsReflBelow deps reflFramesBelow)
    deps.(_extraDeps))
  (idReflRestrFrames: mkIdReflRestrFrameBelowTypes (toDepsReflBelow deps reflFramesBelow)):
  Type :=
  forall i (Hi: i <= k) (ε: arity)
    (d: FramePrev deps.(_deps))
    (c: PaintingPrev deps.(_deps) d),
  rew [PaintingPrev deps.(_deps)] idReflRestrFrames.2 i Hi ε d in
  deps.(_restrPaintings).2 i Hi ε
    (reflFramesBelow.2 i Hi d) (reflPaintingsBelow.2 i Hi d c) = c.

Fixpoint mkIdReflRestrPaintingBelowTypes {p}:
  forall {k} (deps: DepsCohs p k)
    (reflFramesBelow: mkReflFrameBelowTypes deps.(_deps))
    (reflPaintingsBelow: mkReflPaintingBelowTypes (toDepsReflBelow deps reflFramesBelow)
      deps.(_extraDeps))
    (idReflRestrFrames: mkIdReflRestrFrameBelowTypes (toDepsReflBelow deps reflFramesBelow)),
  Type :=
  match p with
  | 0 => fun _ _ _ _ _ => unit
  | S p =>
    fun k deps reflFramesBelow reflPaintingsBelow idReflRestrFrames =>
    { _: mkIdReflRestrPaintingBelowTypes deps.(1) reflFramesBelow.1 reflPaintingsBelow.1 idReflRestrFrames.1 &T
      mkIdReflRestrPaintingBelowType deps reflFramesBelow reflPaintingsBelow
        idReflRestrFrames }
  end.

Class DepsReflCohs p k := {
  _depsCohs2: DepsCohs2 p k;
  _reflFramesBelow': mkReflFrameBelowTypes _depsCohs.(_deps);
  _reflFramesAbove: mkReflFrameAboveTypes _depsCohs.(_deps);
  _reflPaintingsBelow: mkReflPaintingBelowTypes
    (toDepsReflBelow _depsCohs _reflFramesBelow') _depsCohs.(_extraDeps);
  _idReflRestrFramesBelow: mkIdReflRestrFrameBelowTypes
    (toDepsReflBelow _depsCohs _reflFramesBelow');
  _idReflRestrPaintingsBelow: mkIdReflRestrPaintingBelowTypes _depsCohs _reflFramesBelow' _reflPaintingsBelow _idReflRestrFramesBelow;
  _cohReflRestrFramesBelowInf: mkCohReflRestrFrameBelowInfTypes _depsCohs _reflFramesBelow' _reflPaintingsBelow
}.

#[local]
Instance proj1DepsReflCohs {p k} (depsCohs: DepsReflCohs p.+1 k): DepsReflCohs p k.+1 :=
{|
  _depsCohs2 := (depsCohs.(_depsCohs2)).(1);
  _reflFramesBelow' := depsCohs.(_reflFramesBelow').1;
  _reflFramesAbove := depsCohs.(_reflFramesAbove).1;
  _reflPaintingsBelow := depsCohs.(_reflPaintingsBelow).1;
  _idReflRestrFramesBelow := depsCohs.(_idReflRestrFramesBelow).1;
  _idReflRestrPaintingsBelow := depsCohs.(_idReflRestrPaintingsBelow).1;
  _cohReflRestrFramesBelowInf := depsCohs.(_cohReflRestrFramesBelowInf).1;
|}.

Declare Scope depsreflcohs_scope.
Delimit Scope depsreflcohs_scope with depsreflcohs.
Bind Scope depsreflcohs_scope with DepsReflCohs.
Notation "x .(1)" := (proj1DepsReflCohs x%_depsreflcohs)
  (at level 1, left associativity, format "x .(1)"): depsreflcohs_scope.

Definition ReflBelowOfReflCohs {p k}
  (depsCohs: DepsReflCohs p k): DepsReflBelow p k :=
{|
  _depsRestr := depsCohs.(_depsCohs2).(_depsCohs).(_deps);
  _reflFramesBelow := depsCohs.(_reflFramesBelow');
|}.

Definition RestrOfReflCohs {p k}
  (depsCohs: DepsReflCohs p k): DepsRestr p k :=
  (ReflBelowOfReflCohs depsCohs).(_depsRestr).

Definition CohsOfReflCohs {p k}
  (depsCohs: DepsReflCohs p k): DepsCohs p k :=
  depsCohs.(_depsCohs2).(_depsCohs).

Definition RestrExtOfReflCohs {p k}
  (depsCohs: DepsReflCohs p k): DepsRestrExtension p k
    (RestrOfReflCohs depsCohs) :=
  depsCohs.(_depsCohs2).(_depsCohs).(_extraDeps).

Definition CohsExtOfReflCohs {p k}
  (depsCohs: DepsReflCohs p k): DepsCohsExtension p k
    (CohsOfReflCohs depsCohs) :=
  depsCohs.(_depsCohs2).(_extraDepsCohs).

Definition mkReflFramesBelow {p k} (deps: DepsReflCohs p k):
  mkReflFrameBelowTypes (mkDepsRestr (CohsOfReflCohs deps)) :=
  (mkCohReflRestrFrameBelowInfTypesAndReflFramesBelow
    deps.(_depsCohs2).(_depsCohs)
    deps.(_reflFramesBelow')
    deps.(_reflPaintingsBelow)).(ReflFramesBelowDef) deps.(_cohReflRestrFramesBelowInf).

Definition mkReflFrameBelow {p k} (deps: DepsReflCohs p k):
  forall i (Hi: i <= k),
  FramePrev (mkDepsRestr (CohsOfReflCohs deps)) ->
  FrameBase (mkDepsRestr (CohsOfReflCohs deps)) :=
  (mkReflFramesBelow deps).2.

Definition mkDepsReflBelow {p k} (deps: DepsReflCohs p k): DepsReflBelow p.+1 k :=
  {| _depsRestr := mkDepsRestr (CohsOfReflCohs deps);
     _reflFramesBelow := mkReflFramesBelow deps
  |}.

Definition mkCohReflRestrFrameBelowSupType {p k}
  (deps: DepsReflCohs p.+1 k): Type :=
  forall q r (Hq: q <= r) (Hr: r <= k) (ε: arity) (d: FrameBase (RestrOfReflCohs deps)),
  deps.(_reflFramesBelow').2 q (Hq ↕ Hr) ((RestrOfReflCohs deps).(_restrFrames).2 r Hr ε d) =
  mkRestrFrame r.+1 (⇑ Hr) ε (mkReflFrameBelow deps.(1) q (Hq ↕ ↑ Hr) d).

Fixpoint mkCohReflRestrFrameBelowSupTypes {p}:
  forall {k} (deps: DepsReflCohs p k), Type :=
  match p with
  | 0 => fun _ _ => unit
  | S p =>
    fun k deps =>
    { _: mkCohReflRestrFrameBelowSupTypes deps.(1) &T
      mkCohReflRestrFrameBelowSupType deps }
  end.

Definition mkIdReflRestrLayerBelow {p k}
  (deps: DepsReflCohs p.+1 k)
  i (Hi: i <= k)
  (ε: arity)
  (d: FrameBase (RestrOfReflCohs deps))
  (l: mkLayer (RestrOfReflCohs deps).(_restrFrames) d)
  (prevIdReflRestrFrames: mkIdReflRestrFrameBelowTypes (mkDepsReflBelow deps.(1))):
  rew [mkLayer _] prevIdReflRestrFrames.2 i.+1 (⇑ Hi) ε d in
  mkRestrLayer deps.(_depsCohs2).(_depsCohs).(_restrPaintings)
    (deps.(_depsCohs2).(_depsCohs).(_cohs)) i Hi ε _
      (mkReflLayerBelow deps.(_depsCohs2).(_depsCohs)
        ((ReflBelowOfReflCohs deps).(_reflFramesBelow)) deps.(_reflPaintingsBelow) _
          deps.(_cohReflRestrFramesBelowInf) i Hi d l) = l.
Proof.
  apply functional_extensionality_dep.
  intros θ.
  unfold mkRestrLayer, mkReflLayerBelow.
  rewrite <- (deps.(_idReflRestrPaintingsBelow).2 i Hi ε _ (l θ)).
  rewrite <- map_subst_app, <- map_subst.
  unfold toDepsReflBelow, PaintingPrev, FramePrev, RestrOfReflCohs, mkFrame; simpl.
  rewrite rew_map with
    (P := fun x => deps.(_depsCohs2).(_depsCohs).(_deps).(_paintings).2 x)
    (f := fun x => (deps.(_depsCohs2).(_depsCohs).(_deps).(_restrFrames).2 0 leR_O θ x)).
  rewrite rew_map with
    (P := fun x => deps.(_depsCohs2).(_depsCohs).(_deps).(_paintings).2 x)
    (f := fun x => ((deps.(_depsCohs2).(_depsCohs).(_deps).(
      _restrFrames).2 i Hi ε x))).
  rewrite 2 rew_compose.
  apply rew_swap with (P := fun x =>
    deps.(_depsCohs2).(_depsCohs).(_deps).(_paintings).2 x).
  rewrite rew_app_rl. now trivial.
  now apply (RestrOfReflCohs deps).(_frames).2.(UIP).
Defined.

Fixpoint mkIdReflRestrFramesBelow {p k} (deps: DepsReflCohs p k):
  mkIdReflRestrFrameBelowTypes (mkDepsReflBelow deps).
  destruct p.
  - simpl. unshelve econstructor. now exact tt. now intros i Hi ε [].
  - set (h := mkIdReflRestrFramesBelow p k.+1 deps.(1)%depsreflcohs).
    unshelve econstructor.
    + now apply h.
    + intros i Hi ε [l c].
      unshelve eapply eq_existT_curried.
      * now exact (h.2 i.+1 (⇑ Hi) ε l).
      * now exact (mkIdReflRestrLayerBelow deps i Hi ε l c h).
Defined.

Definition mkIdReflRestrBelowFrame {p k} (deps: DepsReflCohs p k):
  mkIdReflRestrFrameBelowType (mkDepsReflBelow deps) :=
  (mkIdReflRestrFramesBelow deps).2.

Class DepsReflAbove p k := {
  _depsRefl: DepsReflBelow p k;
  _extraDeps: DepsRestrExtension p k _depsRefl.(_depsRestr);
  _reflFramesAbove': mkReflFrameAboveTypes _depsRefl.(_depsRestr);
}.

#[local]
Instance proj1DepsReflAbove {p k}
  (deps: DepsReflAbove p.+1 k): DepsReflAbove p k.+1 :=
{|
  _depsRefl := deps.(_depsRefl).(1)%depsreflbelow;
  _extraDeps := (deps.(_depsRefl).(_depsRestr); deps.(_extraDeps));
  _reflFramesAbove' := deps.(_reflFramesAbove').1;
|}.

Declare Scope depsreflabove_scope.
Delimit Scope depsreflabove_scope with depsreflabove.
Bind Scope depsreflabove_scope with DepsReflAbove.
Notation "x .(1)" := (proj1DepsReflAbove x%depsreflabove)
  (at level 1, left associativity, format "x .(1)"): depsreflabove_scope.

Definition AboveOfReflCohs {p k}
  (depsCohs: DepsReflCohs p k): DepsReflAbove p k :=
{|
  _depsRefl := ReflBelowOfReflCohs depsCohs;
  _extraDeps := RestrExtOfReflCohs depsCohs;
  _reflFramesAbove' := depsCohs.(_reflFramesAbove);
|}.

Definition mkReflPaintingAboveType {p k} (deps: DepsReflAbove p.+1 k) :=
  forall i (Hi: i <= p)
    (d: FramePrev deps.(_depsRefl).(_depsRestr))
    (c: PaintingPrev deps.(_depsRefl).(_depsRestr) d),
  mkPainting deps.(_extraDeps) (deps.(_reflFramesAbove').2 i Hi d c).

Fixpoint mkReflPaintingAboveTypes {p}:
  forall {k} (deps: DepsReflAbove p k), Type :=
  match p with
  | 0 => fun _ _ => unit
  | S p =>
    fun k deps =>
    { _: mkReflPaintingAboveTypes deps.(1) &T
      mkReflPaintingAboveType deps }
  end.

Class CohReflRestrFrameAboveSupTypeBlock {p k} (deps: DepsRestr p k) := {
  CohReflRestrFrameAboveSupTypesDef: Type;
  ReflFramesAboveDef: CohReflRestrFrameAboveSupTypesDef -> mkReflFrameAboveTypes deps;
}.

Definition mkCohReflRestrFrameAboveSupTypesStep {p k} (deps: DepsReflCohs p.+1 k)
  (prev: CohReflRestrFrameAboveSupTypeBlock (mkDepsRestr (CohsOfReflCohs deps.(1)))): Type :=
  { Q: prev.(CohReflRestrFrameAboveSupTypesDef) &T
    forall q r (Hq: q <= p) (Hr: r <= k) (ε: arity)
      (d: FrameBase (RestrOfReflCohs deps))
      (c: PaintingBase (RestrOfReflCohs deps) (RestrExtOfReflCohs deps) d),
    deps.(_reflFramesAbove).2 q Hq _ ((CohsOfReflCohs deps).(_restrPaintings).2 r Hr ε d c) =
    mkRestrFrame r Hr ε (((prev.(ReflFramesAboveDef) Q).2) q Hq d c) }.

Definition mkReflLayerAbove {p k} (deps: DepsReflCohs p.+1 k)
  (reflPaintingsAbove: mkReflPaintingAboveTypes (AboveOfReflCohs deps))
  (prev: CohReflRestrFrameAboveSupTypeBlock (mkDepsRestr (CohsOfReflCohs deps.(1))))
  (cohFrames: mkCohReflRestrFrameAboveSupTypesStep deps prev)
  i (Hi: i <= p)
  (d: FrameBase (RestrOfReflCohs deps))
  (c: PaintingBase (RestrOfReflCohs deps) (RestrExtOfReflCohs deps) d):
  mkLayer
    (paintings := mkPaintings (RestrExtOfReflCohs deps))
    (mkDepsRestr (CohsOfReflCohs deps)).(_restrFrames)
    ((prev.(ReflFramesAboveDef) cohFrames.1).2 i Hi d c) :=
  fun ε =>
    rew [(mkDepsRestr (CohsOfReflCohs deps)).(_paintings).2]
      cohFrames.2 i 0 Hi leR_O ε d c in
  reflPaintingsAbove.2 i Hi _
    ((CohsOfReflCohs deps).(_restrPaintings).2 0 leR_O ε d c).

Fixpoint mkCohReflRestrFrameAboveSupTypesAndReflFramesAbove {p k}:
  forall (deps: DepsReflCohs p k)
    (reflPaintingsAbove: mkReflPaintingAboveTypes (AboveOfReflCohs deps)),
    CohReflRestrFrameAboveSupTypeBlock (mkDepsRestr (CohsOfReflCohs deps)) :=
  match p with
  | 0 => fun deps reflPaintingsAbove =>
    {|
      CohReflRestrFrameAboveSupTypesDef := unit;
      ReflFramesAboveDef _ :=
        let reflFrameAbove i (Hi: i <= 0)
          (d: FramePrev (mkDepsRestr (CohsOfReflCohs deps)))
          (c: PaintingPrev (mkDepsRestr (CohsOfReflCohs deps)) d) :=
          (mkReflFrameBelow deps 0 leR_O d;
            fun ε => rew <- mkIdReflRestrBelowFrame deps 0 leR_O ε d in c) in
        ((tt; reflFrameAbove): mkReflFrameAboveTypes (mkDepsRestr (CohsOfReflCohs deps)))
    |}
  | S p => fun deps reflPaintingsAbove =>
    let prev := mkCohReflRestrFrameAboveSupTypesAndReflFramesAbove deps.(1)
      reflPaintingsAbove.1 in
    {|
      CohReflRestrFrameAboveSupTypesDef := mkCohReflRestrFrameAboveSupTypesStep deps prev;
      ReflFramesAboveDef Q :=
        let prevReflFrames := prev.(ReflFramesAboveDef) Q.1 in
        let reflFrameAbove i (Hi: i <= p.+1)
          (d: FramePrev (mkDepsRestr (CohsOfReflCohs deps)))
          (c: PaintingPrev (mkDepsRestr (CohsOfReflCohs deps)) d) :=
          match i return i <= p.+1 -> mkFrame (mkDepsRestr (CohsOfReflCohs deps)) with
          | 0 => fun _ =>
            (mkReflFrameBelow deps 0 leR_O d;
              fun ε => rew <- mkIdReflRestrBelowFrame deps 0 leR_O ε d in c)
          | i.+1 => fun Hi =>
            (prevReflFrames.2 i Hi d.1 (d.2; c);
              mkReflLayerAbove deps reflPaintingsAbove prev Q i (⇓ Hi) d.1 (d.2; c))
          end Hi in
        (prevReflFrames; reflFrameAbove):
          mkReflFrameAboveTypes (mkDepsRestr (CohsOfReflCohs deps))
    |}
  end.

Definition mkCohReflRestrFrameAboveSupTypes {p k}
  (deps: DepsReflCohs p k)
  (reflPaintingsAbove: mkReflPaintingAboveTypes (AboveOfReflCohs deps)): Type :=
  (mkCohReflRestrFrameAboveSupTypesAndReflFramesAbove deps
    reflPaintingsAbove).(CohReflRestrFrameAboveSupTypesDef).

Class DepsReflCohs2 p k := {
  _depsReflCohs: DepsReflCohs p k;
  _reflPaintingsAbove: mkReflPaintingAboveTypes (AboveOfReflCohs _depsReflCohs);
  _cohReflRestrFramesAboveSup:
    mkCohReflRestrFrameAboveSupTypes _depsReflCohs _reflPaintingsAbove;
}.

#[local]
Instance proj1DepsReflCohs2 {p k} (depsCohs2: DepsReflCohs2 p.+1 k):
  DepsReflCohs2 p k.+1 :=
{|
  _depsReflCohs := depsCohs2.(_depsReflCohs).(1)%depsreflcohs;
  _reflPaintingsAbove := depsCohs2.(_reflPaintingsAbove).1;
  _cohReflRestrFramesAboveSup := depsCohs2.(_cohReflRestrFramesAboveSup).1;
|}.

Declare Scope depsreflcohs2_scope.
Delimit Scope depsreflcohs2_scope with depsreflcohs2.
Bind Scope depsreflcohs2_scope with DepsReflCohs2.
Notation "x .(1)" := (proj1DepsReflCohs2 x%depsreflcohs2)
  (at level 1, left associativity, format "x .(1)"): depsreflcohs2_scope.

Definition ReflBelowOfReflCohs2 {p k}
  (depsCohs2: DepsReflCohs2 p k): DepsReflBelow p k :=
  ReflBelowOfReflCohs depsCohs2.(_depsReflCohs).

Definition RestrOfReflCohs2 {p k}
  (depsCohs2: DepsReflCohs2 p k): DepsRestr p k :=
  RestrOfReflCohs depsCohs2.(_depsReflCohs).

Definition CohsOfReflCohs2 {p k}
  (depsCohs2: DepsReflCohs2 p k): DepsCohs p k :=
  CohsOfReflCohs depsCohs2.(_depsReflCohs).

Definition Cohs2OfReflCohs2 {p k}
  (depsCohs2: DepsReflCohs2 p k): DepsCohs2 p k :=
 depsCohs2.(_depsReflCohs).(_depsCohs2).

Definition RestrExtOfReflCohs2 {p k}
  (depsCohs2: DepsReflCohs2 p k): DepsRestrExtension p k
    (RestrOfReflCohs2 depsCohs2) :=
  RestrExtOfReflCohs depsCohs2.(_depsReflCohs).

Definition CohsExtOfReflCohs2 {p k}
  (depsCohs2: DepsReflCohs2 p k): DepsCohsExtension p k
    (CohsOfReflCohs2 depsCohs2) :=
  CohsExtOfReflCohs depsCohs2.(_depsReflCohs).

Definition mkReflFramesAbove {p k} (deps: DepsReflCohs2 p k):
  mkReflFrameAboveTypes (mkDepsRestr (CohsOfReflCohs2 deps)) :=
  (mkCohReflRestrFrameAboveSupTypesAndReflFramesAbove deps.(_depsReflCohs)
    deps.(_reflPaintingsAbove)).(ReflFramesAboveDef)
      deps.(_cohReflRestrFramesAboveSup).

Definition mkReflFrameAbove {p k} (deps: DepsReflCohs2 p k):
  forall i (Hi: i <= p)
    (d: FramePrev (mkDepsRestr (CohsOfReflCohs2 deps)))
    (c: PaintingPrev (mkDepsRestr (CohsOfReflCohs2 deps)) d),
  mkFrame (mkDepsRestr (CohsOfReflCohs2 deps)) :=
  (mkReflFramesAbove deps).2.

Definition mkDepsReflAbove {p k}
  (depsCohs2: DepsReflCohs2 p k): DepsReflAbove p.+1 k :=
{|
  _depsRefl := mkDepsReflBelow depsCohs2.(_depsReflCohs);
  _extraDeps := mkExtraDeps (CohsExtOfReflCohs2 depsCohs2);
  _reflFramesAbove' := mkReflFramesAbove depsCohs2;
|}.

Definition HasRefl {p} (deps: DepsReflCohs2 p 0)
  (E: mkFrame (mkDepsRestr (CohsOfReflCohs2 deps)) -> HSet): Type :=
  forall i (Hi: i <= p)
    (d: FramePrev (mkDepsRestr (CohsOfReflCohs2 deps)))
    (c: PaintingPrev (mkDepsRestr (CohsOfReflCohs2 deps)) d),
  E (mkReflFrameAbove deps i Hi d c).

Inductive DepsReflCohs2Extension p: forall k (deps: DepsReflCohs2 p k), Type :=
| TopReflCoh2Dep {deps: DepsReflCohs2 p 0}
  (L: HasRefl deps (mkPaintings (mkExtraDeps (CohsExtOfReflCohs2 deps))).2):
  DepsReflCohs2Extension p 0 deps
| AddReflCoh2Dep {k} (deps: DepsReflCohs2 p.+1 k):
  DepsReflCohs2Extension p.+1 k deps -> DepsReflCohs2Extension p k.+1 deps.(1).

Arguments TopReflCoh2Dep {p deps}.
Arguments AddReflCoh2Dep {p k}.

Declare Scope extra_depsreflcohs2_scope.
Delimit Scope extra_depsreflcohs2_scope with extradepsreflcohs2.
Bind Scope extra_depsreflcohs2_scope with DepsReflCohs2Extension.
Notation "( x ; y )" := (AddReflCoh2Dep x y)
  (at level 0, format "( x ; y )"): extra_depsreflcohs2_scope.

Fixpoint mkReflPaintingAbove {p k}
  (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkReflPaintingAboveType (mkDepsReflAbove deps).
Proof.
  intros i Hi d c.
  destruct extraDeps.
  - now exact (L i Hi d c).
  - destruct c as [l c'].
    unshelve econstructor.
    + now apply (mkReflLayerAbove _ deps.(_reflPaintingsAbove)).
    + now exact (mkReflPaintingAbove p.+1 k deps extraDeps i.+1 (⇑ Hi) (d; l) c').
Defined.

Fixpoint mkReflPaintingsAbovePrefix {p k}:
  forall (deps: DepsReflCohs2 p k) (extraDeps: DepsReflCohs2Extension p k deps),
  mkReflPaintingAboveTypes ((mkDepsReflAbove deps).(1)) :=
  match p with
  | 0 => fun _ _ => tt
  | S p =>
    fun deps extraDeps =>
      (mkReflPaintingsAbovePrefix deps.(1) (deps; extraDeps);
       mkReflPaintingAbove deps.(1) (deps; extraDeps))
  end.

Definition mkReflPaintingsAbove {p k}:
  forall (deps: DepsReflCohs2 p k) (extraDeps: DepsReflCohs2Extension p k deps),
  mkReflPaintingAboveTypes (mkDepsReflAbove deps) :=
  fun deps extraDeps =>
    (mkReflPaintingsAbovePrefix deps extraDeps; mkReflPaintingAbove deps extraDeps).

Fixpoint mkReflPaintingBelow {p k}
  (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkReflPaintingBelowType
    (mkDepsReflBelow deps.(_depsReflCohs))
    (mkExtraDeps (CohsExtOfReflCohs2 deps)).
Proof.
  intros i Hi d c.
  destruct i.
  - unshelve econstructor.
    + intros ε.
      rewrite (mkIdReflRestrBelowFrame deps.(_depsReflCohs) 0 leR_O ε d).
      now exact c.
    + refine (rew _ in mkReflPaintingAbove deps extraDeps 0 leR_O d c).
      f_equal.
      unfold mkDepsReflAbove, mkDepsReflBelow; simpl. 
      Fail reflexivity.
      now destruct p.
  - destruct extraDeps; [now contradiction |].
    destruct c as [l c'].
    unshelve econstructor.
    + now exact (mkReflLayerBelow _ _
        deps.(_depsReflCohs).(_reflPaintingsBelow) _ _ i Hi d l).
    + now exact (mkReflPaintingBelow p.+1 k deps extraDeps i (⇓ Hi) (d; l) c').
Defined.

Fixpoint mkReflPaintingsBelowPrefix {p k}:
  forall (deps: DepsReflCohs2 p k) (extraDeps: DepsReflCohs2Extension p k deps),
  mkReflPaintingBelowTypes
    ((mkDepsReflBelow deps.(_depsReflCohs)).(1))
    (mkDepsRestr (CohsOfReflCohs2 deps);
    mkExtraDeps (CohsExtOfReflCohs2 deps)) :=
  match p with
  | 0 => fun _ _ => tt
  | S p =>
    fun deps extraDeps =>
      (mkReflPaintingsBelowPrefix deps.(1) (deps; extraDeps);
       mkReflPaintingBelow deps.(1) (deps; extraDeps))
  end.

Definition mkReflPaintingsBelow {p k}:
  forall (deps: DepsReflCohs2 p k) (extraDeps: DepsReflCohs2Extension p k deps),
  mkReflPaintingBelowTypes
    (mkDepsReflBelow deps.(_depsReflCohs))
    (mkExtraDeps (CohsExtOfReflCohs2 deps)) :=
  fun deps extraDeps =>
    (mkReflPaintingsBelowPrefix deps extraDeps; mkReflPaintingBelow deps extraDeps).

Definition mkCohReflRestrPaintingBelowInfType {p k}
  (deps: DepsReflCohs2 p.+1 k)
  (extraDeps: DepsReflCohs2Extension p.+1 k deps): Type :=
  forall q r (Hq: q <= k) (Hr: r <= q) (ε: arity)
    (d: FrameBase (RestrOfReflCohs2 deps))
    (c: PaintingBase (RestrOfReflCohs2 deps) (RestrExtOfReflCohs2 deps) d),
  rew [PaintingBase (RestrOfReflCohs2 deps) (RestrExtOfReflCohs2 deps)]
  deps.(_depsReflCohs).(_cohReflRestrFramesBelowInf).2 q r Hq Hr ε d in
  deps.(_depsReflCohs).(_reflPaintingsBelow).2 q Hq
    ((RestrOfReflCohs2 deps).(_restrFrames).2 r (Hr ↕ Hq) ε d)
    ((CohsOfReflCohs2 deps).(_restrPaintings).2 r (Hr ↕ Hq) ε d c) =
  mkRestrPainting (CohsExtOfReflCohs2 deps.(1)) r (Hr ↕ ↑ Hq) ε
    (mkReflFrameBelow deps.(_depsReflCohs).(1) q.+1 (⇑ Hq) d)
    (mkReflPaintingBelow deps.(1) (deps; extraDeps) q.+1 (⇑ Hq) d c).

Fixpoint mkCohReflRestrPaintingBelowInfTypes {p}:
  forall {k} (deps: DepsReflCohs2 p k)
    (extraDeps: DepsReflCohs2Extension p k deps), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k deps extraDeps =>
    { _: mkCohReflRestrPaintingBelowInfTypes deps.(1) (deps; extraDeps)
      &T mkCohReflRestrPaintingBelowInfType deps extraDeps }
  end.

Definition mkCohReflRestrPaintingBelowSupType {p k}
  (deps: DepsReflCohs2 p.+1 k)
  (extraDeps: DepsReflCohs2Extension p.+1 k deps)
  (cohFramesBelowSup: mkCohReflRestrFrameBelowSupType deps.(_depsReflCohs)): Type :=
  forall q r (Hq: q <= r) (Hr: r <= k) (ε: arity)
    (d: FrameBase (RestrOfReflCohs2 deps))
    (c: PaintingBase (RestrOfReflCohs2 deps) (RestrExtOfReflCohs2 deps) d),
  rew [PaintingBase (RestrOfReflCohs2 deps) (RestrExtOfReflCohs2 deps)]
    cohFramesBelowSup q r Hq Hr ε d in
  deps.(_depsReflCohs).(_reflPaintingsBelow).2 q (Hq ↕ Hr)
    ((RestrOfReflCohs2 deps).(_restrFrames).2 r Hr ε d)
    ((CohsOfReflCohs2 deps).(_restrPaintings).2 r Hr ε d c) =
  mkRestrPainting (CohsExtOfReflCohs2 deps.(1)) r.+1 (⇑ Hr) ε
    (mkReflFrameBelow deps.(_depsReflCohs).(1) q (Hq ↕ ↑ Hr) d)
    (mkReflPaintingBelow deps.(1) (deps; extraDeps) q (Hq ↕ ↑ Hr) d c).

Fixpoint mkCohReflRestrPaintingBelowSupTypes {p}:
  forall {k} (deps: DepsReflCohs2 p k)
    (extraDeps: DepsReflCohs2Extension p k deps)
    (cohFramesBelowSup: mkCohReflRestrFrameBelowSupTypes deps.(_depsReflCohs)),
  Type :=
  match p with
  | 0 => fun _ _ _ _ => unit
  | S p =>
    fun k deps extraDeps cohFramesBelowSup =>
    { _: mkCohReflRestrPaintingBelowSupTypes deps.(1) (deps; extraDeps)
        cohFramesBelowSup.1
      &T mkCohReflRestrPaintingBelowSupType deps extraDeps cohFramesBelowSup.2 }
  end.

Definition mkCohReflRestrPaintingAboveSupType {p k}
  (deps: DepsReflCohs2 p.+1 k)
  (extraDeps: DepsReflCohs2Extension p.+1 k deps): Type :=
  forall q r (Hq: q <= p) (Hr: r <= k) (ε: arity)
    (d: FrameBase (RestrOfReflCohs2 deps))
    (c: PaintingBase (RestrOfReflCohs2 deps) (RestrExtOfReflCohs2 deps) d),
  rew [mkPainting (RestrExtOfReflCohs2 deps)]
    deps.(_cohReflRestrFramesAboveSup).2 q r Hq Hr ε d c in
  deps.(_reflPaintingsAbove).2 q Hq _
    ((CohsOfReflCohs2 deps).(_restrPaintings).2 r Hr ε d c) =
  mkRestrPainting (CohsExtOfReflCohs2 deps) r Hr ε
    (mkReflFrameAbove deps.(1) q Hq d c)
    (mkReflPaintingAbove deps.(1) (deps; extraDeps) q Hq d c).

Fixpoint mkCohReflRestrPaintingAboveSupTypes {p}:
  forall {k}
    (deps: DepsReflCohs2 p k)
    (extraDeps: DepsReflCohs2Extension p k deps), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k deps extraDeps =>
    { _: mkCohReflRestrPaintingAboveSupTypes deps.(1) (deps; extraDeps)
      &T mkCohReflRestrPaintingAboveSupType deps extraDeps }
  end.

Fixpoint mkIdReflRestrPaintingBelow {p k}
  (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkIdReflRestrPaintingBelowType
    (mkDepsCohs (Cohs2OfReflCohs2 deps))
    (mkReflFramesBelow deps.(_depsReflCohs))
    (mkReflPaintingsBelow deps extraDeps)
    (mkIdReflRestrFramesBelow deps.(_depsReflCohs)).
Proof.
  intros i Hi ε d c.
  destruct i.
  - now rewrite rew_compose, eq_trans_sym_inv_l.
  - destruct extraDeps; [now contradiction |].
    unshelve eapply (eq_existT_curried_dep (Q := mkPainting (RestrExtOfReflCohs2 deps))).
    + now apply (mkIdReflRestrLayerBelow deps.(_depsReflCohs) i Hi ε).
    + destruct c as [l c].
      now exact (mkIdReflRestrPaintingBelow p.+1 k deps extraDeps i (⇓ Hi) ε (d; l) c).
Defined.

Fixpoint mkIdReflRestrPaintingsBelow {p k}:
  forall (deps: DepsReflCohs2 p k) (extraDeps: DepsReflCohs2Extension p k deps),
  mkIdReflRestrPaintingBelowTypes
    (mkDepsCohs (Cohs2OfReflCohs2 deps))
    (mkReflFramesBelow deps.(_depsReflCohs))
    (mkReflPaintingsBelow deps extraDeps)
    (mkIdReflRestrFramesBelow deps.(_depsReflCohs)) :=
  match p with
  | 0 => fun deps extraDeps =>
      (tt; mkIdReflRestrPaintingBelow deps extraDeps)
  | S p =>
      fun deps extraDeps =>
      (mkIdReflRestrPaintingsBelow deps.(1) (deps; extraDeps);
       mkIdReflRestrPaintingBelow deps extraDeps)
  end.

Class DepsReflCohs3 p k := {
  _depsReflCohs2: DepsReflCohs2 p k;
  _extraDepsCohs2: DepsCohs2Extension p k (Cohs2OfReflCohs2 _depsReflCohs2);
  _extraDepsReflCohs2: DepsReflCohs2Extension p k _depsReflCohs2;
  _cohReflRestrFramesBelowSup:
    mkCohReflRestrFrameBelowSupTypes _depsReflCohs2.(_depsReflCohs);
  _cohReflRestrPaintingsBelowInf:
    mkCohReflRestrPaintingBelowInfTypes _depsReflCohs2 _extraDepsReflCohs2;
  _cohReflRestrPaintingsBelowSup:
    mkCohReflRestrPaintingBelowSupTypes _depsReflCohs2 _extraDepsReflCohs2
      _cohReflRestrFramesBelowSup;
  _cohReflRestrPaintingsAboveSup:
    mkCohReflRestrPaintingAboveSupTypes _depsReflCohs2 _extraDepsReflCohs2;
}.

#[local]
Instance proj1DepsReflCohs3 {p k} (depsCohs3: DepsReflCohs3 p.+1 k):
DepsReflCohs3 p k.+1 :=
{|
  _depsReflCohs2 := depsCohs3.(_depsReflCohs2).(1);
  _extraDepsCohs2 := (Cohs2OfReflCohs2 depsCohs3.(_depsReflCohs2);
    depsCohs3.(_extraDepsCohs2));
  _extraDepsReflCohs2 := (depsCohs3.(_depsReflCohs2);
    depsCohs3.(_extraDepsReflCohs2));
  _cohReflRestrFramesBelowSup :=
    depsCohs3.(_cohReflRestrFramesBelowSup).1;
  _cohReflRestrPaintingsBelowInf :=
    depsCohs3.(_cohReflRestrPaintingsBelowInf).1;
  _cohReflRestrPaintingsBelowSup :=
    depsCohs3.(_cohReflRestrPaintingsBelowSup).1;
  _cohReflRestrPaintingsAboveSup :=
    depsCohs3.(_cohReflRestrPaintingsAboveSup).1;
|}.

Declare Scope depsreflcohs3_scope.
Delimit Scope depsreflcohs3_scope with depsreflcohs3.
Bind Scope depsreflcohs3_scope with DepsReflCohs3.
Notation "x .(1)" := (proj1DepsReflCohs3 x%depsreflcohs3)
  (at level 1, left associativity, format "x .(1)"): depsreflcohs3_scope.

Definition ReflBelowOfReflCohs3 {p k}
  (depsCohs3: DepsReflCohs3 p k): DepsReflBelow p k :=
  ReflBelowOfReflCohs2 depsCohs3.(_depsReflCohs2).

Definition RestrOfReflCohs3 {p k}
  (depsCohs3: DepsReflCohs3 p k): DepsRestr p k :=
  RestrOfReflCohs2 depsCohs3.(_depsReflCohs2).

Definition CohsOfReflCohs3 {p k}
  (depsCohs3: DepsReflCohs3 p k): DepsCohs p k :=
  CohsOfReflCohs2 depsCohs3.(_depsReflCohs2).

Definition Cohs2OfReflCohs3 {p k}
  (depsCohs3: DepsReflCohs3 p k): DepsCohs2 p k :=
  Cohs2OfReflCohs2 depsCohs3.(_depsReflCohs2).

Definition RestrExtOfReflCohs3 {p k}
  (depsCohs3: DepsReflCohs3 p k): DepsRestrExtension p k
    (RestrOfReflCohs3 depsCohs3) :=
  RestrExtOfReflCohs2 depsCohs3.(_depsReflCohs2).

Definition CohsExtOfReflCohs3 {p k}
  (depsCohs3: DepsReflCohs3 p k): DepsCohsExtension p k
    (CohsOfReflCohs3 depsCohs3) :=
  CohsExtOfReflCohs2 depsCohs3.(_depsReflCohs2).

(*

Definition mkCohReflRestrLayer {p k}
  (deps: DepsReflCohs2 p.+1 k)
  (ε: arity) i (Hi: i <= k)
  (d: mkFrame (((toDepsReflBelow
    (mkDepsCohs (Cohs2OfReflCohs2 deps))
    (mkReflFrames deps.(_depsReflCohs)))).(_deps).(1).(1)))
  (l: mkLayer (toDepsReflBelow
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

  set (d0 := restrFrame 0 leR_O (toDepsReflBelow
    (mkDepsCohs (Cohs2OfReflCohs2 deps).(1))
    (mkReflFrames deps.(_depsReflCohs).(1))).(_deps) θ d).

  assert (h :
    (mkDepsCohs (Cohs2OfReflCohs2 deps)).(1).(_restrPaintings).2 i (↑ Hi) ε
      (reflFrame (toDepsReflBelow
        (mkDepsCohs (Cohs2OfReflCohs2 deps).(1))
        (mkReflFrames deps.(_depsReflCohs).(1))) d0)
      ((mkReflPaintings deps.(_depsReflCohs).(1)
        (deps.(_depsReflCohs); deps.(_extraDepsRefl))).2 d0 (l θ)) =
    mkRestrPainting (CohsExtOfReflCohs deps.(_depsReflCohs).(1)) i  (↑ Hi) ε
      ((mkDepsReflBelow deps.(_depsReflCohs).(1)).(_reflFrames).2 d0)
      (mkReflPainting deps.(_depsReflCohs).(1)
         (deps.(_depsReflCohs); deps.(_extraDepsRefl)) d0 (l θ)))
  by reflexivity; rewrite h; clear h.

  rewrite <- (deps.(_cohReflRestrPaintings).2 ε i Hi d0 (l θ)).
  rewrite rew_map with
    (P := fun b => (mkDepsRestr (CohsOfReflCohs2 deps).(1)).(_paintings).2 b)
    (f := fun x => (mkDepsRestr (CohsOfReflCohs2 deps).(1)).(_restrFrames).2
      0 leR_O θ x).
  rewrite rew_map with
    (P := fun rf => ReflPaintingBase _ _ rf)
    (f := fun d0 => reflFrame (toDepsReflBelow _ _) d0).
  rewrite rew_map with
    (P := fun b => (mkDepsCohs (Cohs2OfReflCohs2 deps)).(1).(
        _deps).(_paintings).2 b)
    (f := fun d0 => (mkDepsCohs (Cohs2OfReflCohs2 deps)).(1).(
      _deps).(_restrFrames).2 i (↑ Hi) ε d0).
  rewrite 4 rew_compose.
  apply rew_swap with
    (P := fun b => (mkDepsCohs (Cohs2OfReflCohs2 deps)).(1).(
      _deps).(_paintings).2 b).
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
| TopReflCohDep2 {deps: DepsReflCohs2 p 0}
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
  - now trivial.
  - unfold ReflPaintingBase, PaintingBase, toDepsReflBelow; simpl.
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
  (reflFrames: mkReflFrameTypes (dgnDepsRestr C)): DepsReflBelow p 0 :=
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
*)

End νDgnSet.

(*
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
*)
