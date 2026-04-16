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

Definition mkReflFrameAboveType {p k} (deps: DepsRestr p.+1 k): Type :=
  forall i (Hi: i <= p) (d: FramePrev deps), PaintingPrev deps d -> mkFrame deps.

Fixpoint mkReflFrameAboveTypes {p k}: DepsRestr p k -> Type :=
  match p with
  | 0 => fun _ => unit
  | p'.+1 => fun deps =>
    { R: mkReflFrameAboveTypes deps.(1) &T mkReflFrameAboveType deps }
  end.

Class DepsReflBelow p k := {
  _depsRestr: DepsRestr p k;
  _reflFramesBelow: mkReflFrameBelowTypes _depsRestr;
}.

#[local]
Instance proj1DepsReflBelow {p k}
  (deps: DepsReflBelow p.+1 k): DepsReflBelow p k.+1 :=
{|
  _depsRestr := deps.(_depsRestr).(1);
  _reflFramesBelow := deps.(_reflFramesBelow).1;
|}.

Declare Scope depsreflbelow_scope.
Delimit Scope depsreflbelow_scope with depsreflbelow.
Bind Scope depsreflbelow_scope with DepsReflBelow.
Notation "x .(1)" := (proj1DepsReflBelow x%depsreflbelow)
  (at level 1, left associativity, format "x .(1)"): depsreflbelow_scope.

Definition mkIdRestrReflFrameBelowType {p k}
  (deps: DepsReflBelow p.+1 k): Type :=
  forall i (Hi: i <= k) ε (d: FramePrev deps.(_depsRestr)),
  deps.(_depsRestr).(_restrFrames).2 i Hi ε (deps.(_reflFramesBelow).2 i Hi d) = d.

Fixpoint mkIdRestrReflFrameBelowTypes {p}:
  forall {k} (deps: DepsReflBelow p k), Type :=
  match p with
  | 0 => fun _ _ => unit
  | S p =>
    fun k deps =>
    { _: mkIdRestrReflFrameBelowTypes deps.(1) &T
      mkIdRestrReflFrameBelowType deps }
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
        ((tt; reflFrame0): mkReflFrameBelowTypes (mkDepsRestr deps))
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

Definition mkIdRestrReflPaintingBelowType {p k}
  (deps: DepsCohs p.+1 k)
  (reflFramesBelow: mkReflFrameBelowTypes deps.(_deps))
  (reflPaintingsBelow: mkReflPaintingBelowTypes (toDepsReflBelow deps reflFramesBelow)
    deps.(_extraDeps))
  (idRestrReflFrames: mkIdRestrReflFrameBelowTypes (toDepsReflBelow deps reflFramesBelow)):
  Type :=
  forall i (Hi: i <= k) (ε: arity)
    (d: FramePrev deps.(_deps))
    (c: PaintingPrev deps.(_deps) d),
  rew [PaintingPrev deps.(_deps)] idRestrReflFrames.2 i Hi ε d in
  deps.(_restrPaintings).2 i Hi ε
    (reflFramesBelow.2 i Hi d) (reflPaintingsBelow.2 i Hi d c) = c.

Fixpoint mkIdRestrReflPaintingBelowTypes {p}:
  forall {k} (deps: DepsCohs p k)
    (reflFramesBelow: mkReflFrameBelowTypes deps.(_deps))
    (reflPaintingsBelow: mkReflPaintingBelowTypes (toDepsReflBelow deps reflFramesBelow)
      deps.(_extraDeps))
    (idRestrReflFrames: mkIdRestrReflFrameBelowTypes (toDepsReflBelow deps reflFramesBelow)),
  Type :=
  match p with
  | 0 => fun _ _ _ _ _ => unit
  | S p =>
    fun k deps reflFramesBelow reflPaintingsBelow idRestrReflFrames =>
    { _: mkIdRestrReflPaintingBelowTypes deps.(1) reflFramesBelow.1 reflPaintingsBelow.1 idRestrReflFrames.1 &T
      mkIdRestrReflPaintingBelowType deps reflFramesBelow reflPaintingsBelow
        idRestrReflFrames }
  end.

Class DepsReflCohsInf p k := {
  _depsCohs2: DepsCohs2 p k;
  _reflFramesBelow': mkReflFrameBelowTypes _depsCohs.(_deps);
  _reflFramesAbove: mkReflFrameAboveTypes _depsCohs.(_deps);
  _reflPaintingsBelow: mkReflPaintingBelowTypes
    (toDepsReflBelow _depsCohs _reflFramesBelow') _depsCohs.(_extraDeps);
  _idRestrReflFramesBelow: mkIdRestrReflFrameBelowTypes
    (toDepsReflBelow _depsCohs _reflFramesBelow');
  _idRestrReflPaintingsBelow: mkIdRestrReflPaintingBelowTypes _depsCohs _reflFramesBelow' _reflPaintingsBelow _idRestrReflFramesBelow;
  _cohReflRestrFramesBelowInf: mkCohReflRestrFrameBelowInfTypes _depsCohs _reflFramesBelow' _reflPaintingsBelow
}.

#[local]
Instance proj1DepsReflCohsInf {p k} (depsCohs: DepsReflCohsInf p.+1 k): DepsReflCohsInf p k.+1 :=
{|
  _depsCohs2 := (depsCohs.(_depsCohs2)).(1);
  _reflFramesBelow' := depsCohs.(_reflFramesBelow').1;
  _reflFramesAbove := depsCohs.(_reflFramesAbove).1;
  _reflPaintingsBelow := depsCohs.(_reflPaintingsBelow).1;
  _idRestrReflFramesBelow := depsCohs.(_idRestrReflFramesBelow).1;
  _idRestrReflPaintingsBelow := depsCohs.(_idRestrReflPaintingsBelow).1;
  _cohReflRestrFramesBelowInf := depsCohs.(_cohReflRestrFramesBelowInf).1;
|}.

Declare Scope depsreflcohsinf_scope.
Delimit Scope depsreflcohsinf_scope with depsreflcohsinf.
Bind Scope depsreflcohsinf_scope with DepsReflCohsInf.
Notation "x .(1)" := (proj1DepsReflCohsInf x%_depsreflcohsinf)
  (at level 1, left associativity, format "x .(1)"): depsreflcohsinf_scope.

Definition ReflBelowOfReflCohsInf {p k}
  (depsCohs: DepsReflCohsInf p k): DepsReflBelow p k :=
{|
  _depsRestr := depsCohs.(_depsCohs2).(_depsCohs).(_deps);
  _reflFramesBelow := depsCohs.(_reflFramesBelow');
|}.

Definition RestrOfReflCohsInf {p k}
  (depsCohs: DepsReflCohsInf p k): DepsRestr p k :=
  (ReflBelowOfReflCohsInf depsCohs).(_depsRestr).

Definition CohsOfReflCohsInf {p k}
  (depsCohs: DepsReflCohsInf p k): DepsCohs p k :=
  depsCohs.(_depsCohs2).(_depsCohs).

Definition RestrExtOfReflCohsInf {p k}
  (depsCohs: DepsReflCohsInf p k): DepsRestrExtension p k
    (RestrOfReflCohsInf depsCohs) :=
  depsCohs.(_depsCohs2).(_depsCohs).(_extraDeps).

Definition CohsExtOfReflCohsInf {p k}
  (depsCohs: DepsReflCohsInf p k): DepsCohsExtension p k
    (CohsOfReflCohsInf depsCohs) :=
  depsCohs.(_depsCohs2).(_extraDepsCohs).

Definition mkReflFramesBelow {p k} (deps: DepsReflCohsInf p k):
  mkReflFrameBelowTypes (mkDepsRestr (CohsOfReflCohsInf deps)) :=
  (mkCohReflRestrFrameBelowInfTypesAndReflFramesBelow
    deps.(_depsCohs2).(_depsCohs)
    deps.(_reflFramesBelow')
    deps.(_reflPaintingsBelow)).(ReflFramesBelowDef) deps.(_cohReflRestrFramesBelowInf).

Definition mkReflFrameBelow {p k} (deps: DepsReflCohsInf p k):
  forall i (Hi: i <= k),
  FramePrev (mkDepsRestr (CohsOfReflCohsInf deps)) ->
  FrameBase (mkDepsRestr (CohsOfReflCohsInf deps)) :=
  (mkReflFramesBelow deps).2.

Definition mkDepsReflBelow {p k} (deps: DepsReflCohsInf p k): DepsReflBelow p.+1 k :=
  {| _depsRestr := mkDepsRestr (CohsOfReflCohsInf deps);
     _reflFramesBelow := mkReflFramesBelow deps
  |}.

Definition mkCohReflRestrFrameBelowSupType {p k}
  (deps: DepsReflCohsInf p.+1 k): Type :=
  forall q r (Hq: q <= r) (Hr: r <= k) (ε: arity) (d: FrameBase (RestrOfReflCohsInf deps)),
  deps.(_reflFramesBelow').2 q (Hq ↕ Hr) ((RestrOfReflCohsInf deps).(_restrFrames).2 r Hr ε d) =
  mkRestrFrame r.+1 (⇑ Hr) ε (mkReflFrameBelow deps.(1) q (Hq ↕ ↑ Hr) d).

Fixpoint mkCohReflRestrFrameBelowSupTypes {p}:
  forall {k} (deps: DepsReflCohsInf p k), Type :=
  match p with
  | 0 => fun _ _ => unit
  | S p =>
    fun k deps =>
    { _: mkCohReflRestrFrameBelowSupTypes deps.(1) &T
      mkCohReflRestrFrameBelowSupType deps }
  end.

Definition mkIdRestrReflLayerBelow {p k}
  (deps: DepsReflCohsInf p.+1 k)
  i (Hi: i <= k)
  (ε: arity)
  (d: FrameBase (RestrOfReflCohsInf deps))
  (l: mkLayer (RestrOfReflCohsInf deps).(_restrFrames) d)
  (prevIdRestrReflFrames: mkIdRestrReflFrameBelowTypes (mkDepsReflBelow deps.(1))):
  rew [mkLayer _] prevIdRestrReflFrames.2 i.+1 (⇑ Hi) ε d in
  mkRestrLayer deps.(_depsCohs2).(_depsCohs).(_restrPaintings)
    (deps.(_depsCohs2).(_depsCohs).(_cohs)) i Hi ε _
      (mkReflLayerBelow deps.(_depsCohs2).(_depsCohs)
        ((ReflBelowOfReflCohsInf deps).(_reflFramesBelow)) deps.(_reflPaintingsBelow) _
          deps.(_cohReflRestrFramesBelowInf) i Hi d l) = l.
Proof.
  apply functional_extensionality_dep.
  intros θ.
  unfold mkRestrLayer, mkReflLayerBelow.
  rewrite <- (deps.(_idRestrReflPaintingsBelow).2 i Hi ε _ (l θ)).
  rewrite <- map_subst_app, <- map_subst.
  set (deps' := deps.(_depsCohs2).(_depsCohs).(_deps)).
  rewrite rew_map with
    (P := fun x => deps'.(_paintings).2 x)
    (f := fun x => deps'.(_restrFrames).2 0 leR_O θ x).
  rewrite rew_map with
    (P := fun x => deps'.(_paintings).2 x)
    (f := fun x => deps'.(_restrFrames).2 i Hi ε x).
  rewrite 2 rew_compose.
  apply rew_swap with (P := fun x => deps'.(_paintings).2 x).
  rewrite rew_app_rl. now trivial.
  now apply (RestrOfReflCohsInf deps).(_frames).2.(UIP).
Defined.

Fixpoint mkIdRestrReflFramesBelow {p k} (deps: DepsReflCohsInf p k):
  mkIdRestrReflFrameBelowTypes (mkDepsReflBelow deps).
  destruct p.
  - unshelve econstructor.
    now exact tt.
    now intros i Hi ε [].
  - set (h := mkIdRestrReflFramesBelow p k.+1 deps.(1)%depsreflcohsinf).
    unshelve econstructor.
    + now apply h.
    + intros i Hi ε [d l].
      unshelve eapply eq_existT_curried.
      * now exact (h.2 i.+1 (⇑ Hi) ε d).
      * now exact (mkIdRestrReflLayerBelow deps i Hi ε d l h).
Defined.

Definition mkIdRestrReflFrameBelow {p k} (deps: DepsReflCohsInf p k):
  mkIdRestrReflFrameBelowType (mkDepsReflBelow deps) :=
  (mkIdRestrReflFramesBelow deps).2.

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

Definition AboveOfReflCohsInf {p k}
  (depsCohs: DepsReflCohsInf p k): DepsReflAbove p k :=
{|
  _depsRefl := ReflBelowOfReflCohsInf depsCohs;
  _extraDeps := RestrExtOfReflCohsInf depsCohs;
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

Definition mkReflLayerAbove0 {p k} (deps: DepsReflCohsInf p k)
  (d: FramePrev (mkDepsRestr (CohsOfReflCohsInf deps)))
  (c: PaintingPrev (mkDepsRestr (CohsOfReflCohsInf deps)) d):
  mkLayer
    (paintings := (mkDepsRestr (CohsOfReflCohsInf deps)).(_paintings))
    (mkDepsRestr (CohsOfReflCohsInf deps)).(_restrFrames)
    (mkReflFrameBelow deps 0 leR_O d) :=
  fun ε => rew <- mkIdRestrReflFrameBelow deps 0 leR_O ε d in c.

Definition mkReflFrameAbove0 {p k} (deps: DepsReflCohsInf p k)
  (d: FramePrev (mkDepsRestr (CohsOfReflCohsInf deps)))
  (c: PaintingPrev (mkDepsRestr (CohsOfReflCohsInf deps)) d):
  mkFrame (mkDepsRestr (CohsOfReflCohsInf deps)) :=
  (mkReflFrameBelow deps 0 leR_O d; mkReflLayerAbove0 deps d c).

Definition mkReflFrameAboveTypeS {p k} (deps: DepsRestr p.+1 k): Type :=
  forall i (Hi: i.+1 <= p) (d: FramePrev deps),
  PaintingPrev deps d -> mkFrame deps.

Fixpoint mkReflFrameAboveTypesS {p k}: DepsRestr p k -> Type :=
  match p with
  | 0 => fun _ => unit
  | p'.+1 => fun deps =>
    { R: mkReflFrameAboveTypesS deps.(1) &T mkReflFrameAboveTypeS deps }
  end.

Definition mkReflFrameAboveOf0AndS {p k} (deps: DepsReflCohsInf p k)
  (reflFrameAboveS: mkReflFrameAboveTypeS (mkDepsRestr (CohsOfReflCohsInf deps))):
  mkReflFrameAboveType (mkDepsRestr (CohsOfReflCohsInf deps)) :=
  fun i =>
    match i with
    | 0 => fun _ => mkReflFrameAbove0 deps
    | i'.+1 => fun Hi => reflFrameAboveS i' Hi
    end.

Fixpoint mkReflFramesAboveOf0AndSPrefix {p k}:
  forall (deps: DepsReflCohsInf p k)
    (reflFramesAboveS: mkReflFrameAboveTypesS (mkDepsRestr (CohsOfReflCohsInf deps)).(1)),
  mkReflFrameAboveTypes (mkDepsRestr (CohsOfReflCohsInf deps)).(1) :=
  match p with
  | 0 => fun _ _ => tt
  | p'.+1 => fun deps reflFramesAboveS =>
    (mkReflFramesAboveOf0AndSPrefix deps.(1) reflFramesAboveS.1;
     mkReflFrameAboveOf0AndS deps.(1) reflFramesAboveS.2)
  end.

Definition mkReflFramesAboveOf0AndS {p k} (deps: DepsReflCohsInf p k)
  (reflFramesAboveS: mkReflFrameAboveTypesS (mkDepsRestr (CohsOfReflCohsInf deps))):
  mkReflFrameAboveTypes (mkDepsRestr (CohsOfReflCohsInf deps)) :=
  (mkReflFramesAboveOf0AndSPrefix deps reflFramesAboveS.1;
   mkReflFrameAboveOf0AndS deps reflFramesAboveS.2).

Class CohReflRestrFrameAboveSupTypeBlock {p k} (deps: DepsRestr p k) := {
  CohReflRestrFrameAboveSupTypesDef: Type;
  ReflFramesAboveSDef: CohReflRestrFrameAboveSupTypesDef -> mkReflFrameAboveTypesS deps;
}.

Definition mkCohReflRestrFrameAboveSupType {p k} (deps: DepsReflCohsInf p.+1 k)
  (prev: CohReflRestrFrameAboveSupTypeBlock (mkDepsRestr (CohsOfReflCohsInf deps.(1))))
  (Q: prev.(CohReflRestrFrameAboveSupTypesDef)): Type :=
  forall q r (Hq: q <= p) (Hr: r <= k) (ε: arity)
    (d: FrameBase (RestrOfReflCohsInf deps))
    (c: PaintingBase (RestrOfReflCohsInf deps) (RestrExtOfReflCohsInf deps) d),
  let reflFramesAbove := mkReflFramesAboveOf0AndS deps.(1) (prev.(ReflFramesAboveSDef) Q) in
  deps.(_reflFramesAbove).2 q Hq _ ((CohsOfReflCohsInf deps).(_restrPaintings).2 r Hr ε d c) =
  mkRestrFrame r Hr ε ((reflFramesAbove.2) q Hq d c).

Definition mkCohReflRestrFrameAboveSupTypesStep {p k} (deps: DepsReflCohsInf p.+1 k)
  (prev: CohReflRestrFrameAboveSupTypeBlock (mkDepsRestr (CohsOfReflCohsInf deps.(1)))): Type :=
  { Q: prev.(CohReflRestrFrameAboveSupTypesDef) &T
   mkCohReflRestrFrameAboveSupType deps prev Q }.

Definition mkReflLayerAbove {p k} (deps: DepsReflCohsInf p.+1 k)
  (reflPaintingsAbove: mkReflPaintingAboveTypes (AboveOfReflCohsInf deps))
  (prev: CohReflRestrFrameAboveSupTypeBlock (mkDepsRestr (CohsOfReflCohsInf deps.(1))))
  (cohFrames: mkCohReflRestrFrameAboveSupTypesStep deps prev)
  i (Hi: i <= p)
  (d: FrameBase (RestrOfReflCohsInf deps))
  (c: PaintingBase (RestrOfReflCohsInf deps) (RestrExtOfReflCohsInf deps) d):
  let reflFramesAbove := mkReflFramesAboveOf0AndS deps.(1) (prev.(ReflFramesAboveSDef) cohFrames.1) in
  mkLayer
    (paintings := mkPaintings (RestrExtOfReflCohsInf deps))
    (mkDepsRestr (CohsOfReflCohsInf deps)).(_restrFrames)
    (reflFramesAbove.2 i Hi d c) :=
  fun ε =>
    rew [(mkDepsRestr (CohsOfReflCohsInf deps)).(_paintings).2]
      cohFrames.2 i 0 Hi leR_O ε d c in
  reflPaintingsAbove.2 i Hi _
    ((CohsOfReflCohsInf deps).(_restrPaintings).2 0 leR_O ε d c).

Fixpoint mkCohReflRestrFrameAboveSupTypesAndReflFramesAbove {p k}:
  forall (deps: DepsReflCohsInf p k)
    (reflPaintingsAbove: mkReflPaintingAboveTypes (AboveOfReflCohsInf deps)),
    CohReflRestrFrameAboveSupTypeBlock (mkDepsRestr (CohsOfReflCohsInf deps)) :=
  match p with
  | 0 => fun deps reflPaintingsAbove =>
    {|
      CohReflRestrFrameAboveSupTypesDef := unit;
      ReflFramesAboveSDef _ :=
        let reflFrame0: mkReflFrameAboveTypeS (mkDepsRestr (CohsOfReflCohsInf deps)) :=
          fun i Hi d c => match Hi with end in
        ((tt; reflFrame0): mkReflFrameAboveTypesS (mkDepsRestr (CohsOfReflCohsInf deps)))
    |}
  | p'.+1 => fun deps reflPaintingsAbove =>
    let prev := mkCohReflRestrFrameAboveSupTypesAndReflFramesAbove deps.(1) reflPaintingsAbove.1 in
    {|
      CohReflRestrFrameAboveSupTypesDef := mkCohReflRestrFrameAboveSupTypesStep deps prev;
      ReflFramesAboveSDef Q :=
        let prevReflFrames := prev.(ReflFramesAboveSDef) Q.1 in
        let reflFramesAbove := mkReflFramesAboveOf0AndS deps.(1) prevReflFrames in
        let reflFrame i (Hi: i.+1 <= p'.+1) d c :=
          (reflFramesAbove.2 i Hi d.1 (d.2; c);
           mkReflLayerAbove deps reflPaintingsAbove prev Q i (⇓ Hi) d.1 (d.2; c)) in
        (prevReflFrames; reflFrame):
          mkReflFrameAboveTypesS (mkDepsRestr (CohsOfReflCohsInf deps))
    |}
  end.

Definition mkCohReflRestrFrameAboveSupTypes {p k}
  (deps: DepsReflCohsInf p k)
  (reflPaintingsAbove: mkReflPaintingAboveTypes (AboveOfReflCohsInf deps)): Type :=
  (mkCohReflRestrFrameAboveSupTypesAndReflFramesAbove deps
    reflPaintingsAbove).(CohReflRestrFrameAboveSupTypesDef).

Class DepsReflCohsSup p k := {
  _depsReflCohsInf: DepsReflCohsInf p k;
  _cohReflRestrFramesBelowSup:
    mkCohReflRestrFrameBelowSupTypes _depsReflCohsInf;
  _reflPaintingsAbove: mkReflPaintingAboveTypes (AboveOfReflCohsInf _depsReflCohsInf);
  _cohReflRestrFramesAboveSup:
    mkCohReflRestrFrameAboveSupTypes _depsReflCohsInf _reflPaintingsAbove;
}.

#[local]
Instance proj1DepsReflCohsSup {p k} (depsCohsSup: DepsReflCohsSup p.+1 k):
  DepsReflCohsSup p k.+1 :=
{|
  _depsReflCohsInf := depsCohsSup.(_depsReflCohsInf).(1)%depsreflcohsinf;
  _cohReflRestrFramesBelowSup := depsCohsSup.(_cohReflRestrFramesBelowSup).1;
  _reflPaintingsAbove := depsCohsSup.(_reflPaintingsAbove).1;
  _cohReflRestrFramesAboveSup := depsCohsSup.(_cohReflRestrFramesAboveSup).1;
|}.

Declare Scope depsreflcohssup_scope.
Delimit Scope depsreflcohssup_scope with depsreflcohssup.
Bind Scope depsreflcohssup_scope with DepsReflCohsSup.
Notation "x .(1)" := (proj1DepsReflCohsSup x%depsreflcohssup)
  (at level 1, left associativity, format "x .(1)"): depsreflcohssup_scope.

Definition ReflBelowOfReflCohsSup {p k}
  (depsCohsSup: DepsReflCohsSup p k): DepsReflBelow p k :=
  ReflBelowOfReflCohsInf depsCohsSup.(_depsReflCohsInf).

Definition RestrOfReflCohsSup {p k}
  (depsCohsSup: DepsReflCohsSup p k): DepsRestr p k :=
  RestrOfReflCohsInf depsCohsSup.(_depsReflCohsInf).

Definition CohsOfReflCohsSup {p k}
  (depsCohsSup: DepsReflCohsSup p k): DepsCohs p k :=
  CohsOfReflCohsInf depsCohsSup.(_depsReflCohsInf).

Definition Cohs2OfReflCohsSup {p k}
  (depsCohsSup: DepsReflCohsSup p k): DepsCohs2 p k :=
 depsCohsSup.(_depsReflCohsInf).(_depsCohs2).

Definition RestrExtOfReflCohsSup {p k}
  (depsCohsSup: DepsReflCohsSup p k): DepsRestrExtension p k
    (RestrOfReflCohsSup depsCohsSup) :=
  RestrExtOfReflCohsInf depsCohsSup.(_depsReflCohsInf).

Definition CohsExtOfReflCohsSup {p k}
  (depsCohsSup: DepsReflCohsSup p k): DepsCohsExtension p k
    (CohsOfReflCohsSup depsCohsSup) :=
  CohsExtOfReflCohsInf depsCohsSup.(_depsReflCohsInf).

Definition mkReflFramesAboveS {p k} (deps: DepsReflCohsSup p k):
  mkReflFrameAboveTypesS (mkDepsRestr (CohsOfReflCohsSup deps)) :=
  (mkCohReflRestrFrameAboveSupTypesAndReflFramesAbove deps.(_depsReflCohsInf)
    deps.(_reflPaintingsAbove)).(ReflFramesAboveSDef)
      deps.(_cohReflRestrFramesAboveSup).

Definition mkReflFramesAbove {p k} (deps: DepsReflCohsSup p k):
  mkReflFrameAboveTypes (mkDepsRestr (CohsOfReflCohsSup deps)) :=
  mkReflFramesAboveOf0AndS deps.(_depsReflCohsInf) (mkReflFramesAboveS deps).

Definition mkReflFrameAbove {p k} (deps: DepsReflCohsSup p k):
  forall i (Hi: i <= p)
    (d: FramePrev (mkDepsRestr (CohsOfReflCohsSup deps)))
    (c: PaintingPrev (mkDepsRestr (CohsOfReflCohsSup deps)) d),
  mkFrame (mkDepsRestr (CohsOfReflCohsSup deps)) :=
  (mkReflFramesAbove deps).2.

Definition mkDepsReflAbove {p k}
  (depsCohsSup: DepsReflCohsSup p k): DepsReflAbove p.+1 k :=
{|
  _depsRefl := mkDepsReflBelow depsCohsSup.(_depsReflCohsInf);
  _extraDeps := mkExtraDeps (CohsExtOfReflCohsSup depsCohsSup);
  _reflFramesAbove' := mkReflFramesAbove depsCohsSup;
|}.

Definition HasRefl {p} (deps: DepsReflCohsSup p 0)
  (E: mkFrame (mkDepsRestr (CohsOfReflCohsSup deps)) -> HSet): Type :=
  forall i (Hi: i <= p)
    (d: FramePrev (mkDepsRestr (CohsOfReflCohsSup deps)))
    (c: PaintingPrev (mkDepsRestr (CohsOfReflCohsSup deps)) d),
  E (mkReflFrameAbove deps i Hi d c).

Inductive DepsReflCohsSupExtension p: forall k (deps: DepsReflCohsSup p k), Type :=
| TopReflCohSupDep {deps: DepsReflCohsSup p 0}
  (L: HasRefl deps (mkPainting (mkExtraDeps (CohsExtOfReflCohsSup deps)))):
  DepsReflCohsSupExtension p 0 deps
| AddReflCohSupDep {k} (deps: DepsReflCohsSup p.+1 k):
  DepsReflCohsSupExtension p.+1 k deps -> DepsReflCohsSupExtension p k.+1 deps.(1).

Arguments TopReflCohSupDep {p deps}.
Arguments AddReflCohSupDep {p k}.

Declare Scope extra_depsreflcohssup_scope.
Delimit Scope extra_depsreflcohssup_scope with extradepsreflcohssup.
Bind Scope extra_depsreflcohssup_scope with DepsReflCohsSupExtension.
Notation "( x ; y )" := (AddReflCohSupDep x y)
  (at level 0, format "( x ; y )"): extra_depsreflcohssup_scope.

Fixpoint mkReflPaintingAbove {p k}
  (deps: DepsReflCohsSup p k)
  (extraDeps: DepsReflCohsSupExtension p k deps):
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
  forall (deps: DepsReflCohsSup p k) (extraDeps: DepsReflCohsSupExtension p k deps),
  mkReflPaintingAboveTypes ((mkDepsReflAbove deps).(1)) :=
  match p with
  | 0 => fun deps extraDeps => tt
  | S p =>
    fun deps extraDeps =>
      (mkReflPaintingsAbovePrefix deps.(1) (deps; extraDeps);
       mkReflPaintingAbove deps.(1) (deps; extraDeps))
  end.

Definition mkReflPaintingsAbove {p k}:
  forall (deps: DepsReflCohsSup p k) (extraDeps: DepsReflCohsSupExtension p k deps),
  mkReflPaintingAboveTypes (mkDepsReflAbove deps) :=
  fun deps extraDeps =>
    (mkReflPaintingsAbovePrefix deps extraDeps; mkReflPaintingAbove deps extraDeps).

Definition mkReflPaintingBelow1 {p k}
  (deps: DepsReflCohsSup p k)
  (extraDeps: DepsReflCohsSupExtension p k deps)
  i (Hi: i <= k)
  (d: FramePrev (mkDepsReflBelow deps.(_depsReflCohsInf)).(_depsRestr))
  (c: PaintingPrev (mkDepsReflBelow deps.(_depsReflCohsInf)) .(_depsRestr) d) :
  (mkLayer
    (paintings := (mkDepsReflBelow deps.(_depsReflCohsInf)).(_depsRestr).(_paintings))
    (mkDepsReflBelow deps.(_depsReflCohsInf)).(_depsRestr).(_restrFrames)
    ((mkDepsReflBelow deps.(_depsReflCohsInf)).(_reflFramesBelow).2 i Hi d)).
Proof.
  destruct i.
  - now exact (mkReflLayerAbove0 deps.(_depsReflCohsInf) d c).
  - destruct extraDeps; [now contradiction |].
    destruct c as [l c'].
    now exact (mkReflLayerBelow _ _
      deps.(_depsReflCohsInf).(_reflPaintingsBelow) _ _ i Hi d l).
Defined.

Fixpoint mkReflPaintingBelow2 {p k}
  (deps: DepsReflCohsSup p k)
  (extraDeps: DepsReflCohsSupExtension p k deps)
  i (Hi: i <= k)
  (d: FramePrev (mkDepsReflBelow deps.(_depsReflCohsInf)).(_depsRestr))
  (c: PaintingPrev (mkDepsReflBelow deps .(_depsReflCohsInf)) .(_depsRestr) d)
  {struct i} :
  (mkPainting (mkExtraDeps (CohsExtOfReflCohsSup deps))
    (mkReflFrameBelow deps.(_depsReflCohsInf) i Hi d;
    (mkReflPaintingBelow1 deps extraDeps i Hi d c))).
Proof.
  destruct i.
  - now exact (mkReflPaintingAbove deps extraDeps 0 leR_O d c).
  - destruct extraDeps; [now contradiction |].
    destruct c as [l c'].
    unshelve econstructor.
    + now exact (mkReflPaintingBelow1 deps extraDeps i (⇓ Hi) (d; l) c').
    + now exact (mkReflPaintingBelow2 p.+1 k deps extraDeps i (⇓ Hi) (d; l) c').
Defined.

Definition mkReflPaintingBelow {p k}
  (deps: DepsReflCohsSup p k)
  (extraDeps: DepsReflCohsSupExtension p k deps):
  mkReflPaintingBelowType
    (mkDepsReflBelow deps.(_depsReflCohsInf))
    (mkExtraDeps (CohsExtOfReflCohsSup deps)).
Proof.
  intros i Hi d c.
  unshelve econstructor.
  - now exact (mkReflPaintingBelow1 deps extraDeps i Hi d c).
  - now exact (mkReflPaintingBelow2 deps extraDeps i Hi d c).
Defined.

Fixpoint mkReflPaintingsBelowPrefix {p k}:
  forall (deps: DepsReflCohsSup p k) (extraDeps: DepsReflCohsSupExtension p k deps),
  mkReflPaintingBelowTypes
    ((mkDepsReflBelow deps.(_depsReflCohsInf)).(1))
    (mkDepsRestr (CohsOfReflCohsSup deps);
    mkExtraDeps (CohsExtOfReflCohsSup deps)) :=
  match p with
  | 0 => fun _ _ => tt
  | S p =>
    fun deps extraDeps =>
      (mkReflPaintingsBelowPrefix deps.(1) (deps; extraDeps);
       mkReflPaintingBelow deps.(1) (deps; extraDeps))
  end.

Definition mkReflPaintingsBelow {p k}:
  forall (deps: DepsReflCohsSup p k) (extraDeps: DepsReflCohsSupExtension p k deps),
  mkReflPaintingBelowTypes
    (mkDepsReflBelow deps.(_depsReflCohsInf))
    (mkExtraDeps (CohsExtOfReflCohsSup deps)) :=
  fun deps extraDeps =>
    (mkReflPaintingsBelowPrefix deps extraDeps; mkReflPaintingBelow deps extraDeps).

Definition mkCohReflRestrPaintingBelowInfType {p k}
  (deps: DepsReflCohsSup p.+1 k)
  (extraDeps: DepsReflCohsSupExtension p.+1 k deps): Type :=
  forall q r (Hq: q <= k) (Hr: r <= q) (ε: arity)
    (d: FrameBase (RestrOfReflCohsSup deps))
    (c: PaintingBase (RestrOfReflCohsSup deps) (RestrExtOfReflCohsSup deps) d),
  rew [PaintingBase (RestrOfReflCohsSup deps) (RestrExtOfReflCohsSup deps)]
  deps.(_depsReflCohsInf).(_cohReflRestrFramesBelowInf).2 q r Hq Hr ε d in
  deps.(_depsReflCohsInf).(_reflPaintingsBelow).2 q Hq
    ((RestrOfReflCohsSup deps).(_restrFrames).2 r (Hr ↕ Hq) ε d)
    ((CohsOfReflCohsSup deps).(_restrPaintings).2 r (Hr ↕ Hq) ε d c) =
  mkRestrPainting (CohsExtOfReflCohsSup deps.(1)) r (Hr ↕ ↑ Hq) ε
    (mkReflFrameBelow deps.(_depsReflCohsInf).(1) q.+1 (⇑ Hq) d)
    (mkReflPaintingBelow deps.(1) (deps; extraDeps) q.+1 (⇑ Hq) d c).

Fixpoint mkCohReflRestrPaintingBelowInfTypes {p}:
  forall {k} (deps: DepsReflCohsSup p k)
    (extraDeps: DepsReflCohsSupExtension p k deps), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k deps extraDeps =>
    { _: mkCohReflRestrPaintingBelowInfTypes deps.(1) (deps; extraDeps)
      &T mkCohReflRestrPaintingBelowInfType deps extraDeps }
  end.

Definition mkCohReflRestrPaintingBelowSupType {p k}
  (deps: DepsReflCohsSup p.+1 k)
  (extraDeps: DepsReflCohsSupExtension p.+1 k deps): Type :=
  forall q r (Hq: q <= r) (Hr: r <= k) (ε: arity)
    (d: FrameBase (RestrOfReflCohsSup deps))
    (c: PaintingBase (RestrOfReflCohsSup deps) (RestrExtOfReflCohsSup deps) d),
  rew [PaintingBase (RestrOfReflCohsSup deps) (RestrExtOfReflCohsSup deps)]
    deps.(_cohReflRestrFramesBelowSup).2 q r Hq Hr ε d in
  deps.(_depsReflCohsInf).(_reflPaintingsBelow).2 q (Hq ↕ Hr)
    ((RestrOfReflCohsSup deps).(_restrFrames).2 r Hr ε d)
    ((CohsOfReflCohsSup deps).(_restrPaintings).2 r Hr ε d c) =
  mkRestrPainting (CohsExtOfReflCohsSup deps.(1)) r.+1 (⇑ Hr) ε
    (mkReflFrameBelow deps.(_depsReflCohsInf).(1) q (Hq ↕ ↑ Hr) d)
    (mkReflPaintingBelow deps.(1) (deps; extraDeps) q (Hq ↕ ↑ Hr) d c).

Fixpoint mkCohReflRestrPaintingBelowSupTypes {p}:
  forall {k} (deps: DepsReflCohsSup p k)
    (extraDeps: DepsReflCohsSupExtension p k deps),
  Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k deps extraDeps =>
    { _: mkCohReflRestrPaintingBelowSupTypes deps.(1) (deps; extraDeps)
      &T mkCohReflRestrPaintingBelowSupType deps extraDeps}
  end.

Definition mkCohReflRestrPaintingAboveSupType {p k}
  (deps: DepsReflCohsSup p.+1 k)
  (extraDeps: DepsReflCohsSupExtension p.+1 k deps): Type :=
  forall q r (Hq: q <= p) (Hr: r <= k) (ε: arity)
    (d: FrameBase (RestrOfReflCohsSup deps))
    (c: PaintingBase (RestrOfReflCohsSup deps) (RestrExtOfReflCohsSup deps) d),
  rew [mkPainting (RestrExtOfReflCohsSup deps)]
    deps.(_cohReflRestrFramesAboveSup).2 q r Hq Hr ε d c in
  deps.(_reflPaintingsAbove).2 q Hq _
    ((CohsOfReflCohsSup deps).(_restrPaintings).2 r Hr ε d c) =
  mkRestrPainting (CohsExtOfReflCohsSup deps) r Hr ε
    (mkReflFrameAbove deps.(1) q Hq d c)
    (mkReflPaintingAbove deps.(1) (deps; extraDeps) q Hq d c).

Fixpoint mkCohReflRestrPaintingAboveSupTypes {p}:
  forall {k}
    (deps: DepsReflCohsSup p k)
    (extraDeps: DepsReflCohsSupExtension p k deps), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k deps extraDeps =>
    { _: mkCohReflRestrPaintingAboveSupTypes deps.(1) (deps; extraDeps)
      &T mkCohReflRestrPaintingAboveSupType deps extraDeps }
  end.

Fixpoint mkIdRestrReflPaintingBelow {p k}
  (deps: DepsReflCohsSup p k)
  (extraDeps: DepsReflCohsSupExtension p k deps):
  mkIdRestrReflPaintingBelowType
    (mkDepsCohs (Cohs2OfReflCohsSup deps))
    (mkReflFramesBelow deps.(_depsReflCohsInf))
    (mkReflPaintingsBelow deps extraDeps)
    (mkIdRestrReflFramesBelow deps.(_depsReflCohsInf)).
Proof.
  intros i Hi ε d c.
  destruct i.
  - now rewrite rew_compose, eq_trans_sym_inv_l.
  - destruct extraDeps; [now contradiction |].
    unshelve eapply (eq_existT_curried_dep (Q := mkPainting (RestrExtOfReflCohsSup deps))).
    + now apply (mkIdRestrReflLayerBelow deps.(_depsReflCohsInf) i Hi ε).
    + destruct c as [l c].
      now exact (mkIdRestrReflPaintingBelow p.+1 k deps extraDeps i (⇓ Hi) ε (d; l) c).
Defined.

Fixpoint mkIdRestrReflPaintingsBelow {p k}:
  forall (deps: DepsReflCohsSup p k) (extraDeps: DepsReflCohsSupExtension p k deps),
  mkIdRestrReflPaintingBelowTypes
    (mkDepsCohs (Cohs2OfReflCohsSup deps))
    (mkReflFramesBelow deps.(_depsReflCohsInf))
    (mkReflPaintingsBelow deps extraDeps)
    (mkIdRestrReflFramesBelow deps.(_depsReflCohsInf)) :=
  match p with
  | 0 => fun deps extraDeps =>
      (tt; mkIdRestrReflPaintingBelow deps extraDeps)
  | S p =>
      fun deps extraDeps =>
      (mkIdRestrReflPaintingsBelow deps.(1) (deps; extraDeps);
       mkIdRestrReflPaintingBelow deps extraDeps)
  end.

Definition mkCohReflBelowBelowFrameType {p k}
  (deps: DepsReflCohsInf p.+1 k): Type :=
  forall q r (Hq: q <= r) (Hr: r <= k) (d: FramePrev (RestrOfReflCohsInf deps)),
  (mkReflFrameBelow deps.(1) q (Hq ↕ ↑ Hr) (deps.(_reflFramesBelow').2 r Hr d)) =
  (mkReflFrameBelow deps.(1) r.+1 (⇑ Hr) (deps.(_reflFramesBelow').2 q (Hq ↕ Hr) d)).

Fixpoint mkCohReflBelowBelowFrameTypes {p}:
  forall {k} (deps: DepsReflCohsInf p k), Type :=
  match p with
  | 0 => fun _ _ => unit
  | S p =>
    fun k deps =>
    { _: mkCohReflBelowBelowFrameTypes deps.(1) &T
      mkCohReflBelowBelowFrameType deps }
  end.

Definition mkCohReflAboveBelowFrameType {p k}
  (deps: DepsReflCohsSup p.+1 k): Type :=
  forall q r (Hq: q <= p) (Hr: r <= k)
    (d: FramePrev (RestrOfReflCohsSup deps))
    (c: PaintingPrev (RestrOfReflCohsSup deps) d),
  mkReflFrameAbove deps.(1)%depsreflcohssup q Hq
    (deps.(_depsReflCohsInf).(_reflFramesBelow').2 r Hr d)
    (deps.(_depsReflCohsInf).(_reflPaintingsBelow).2 r Hr d c) =
  mkReflFrameBelow deps.(_depsReflCohsInf) r Hr
    (deps.(_depsReflCohsInf).(_reflFramesAbove).2 q Hq d c).

Fixpoint mkCohReflAboveBelowFrameTypes {p}:
  forall {k} (deps: DepsReflCohsSup p k), Type :=
  match p with
  | 0 => fun _ _ => unit
  | S p =>
    fun k deps =>
    { _: mkCohReflAboveBelowFrameTypes deps.(1) &T
      mkCohReflAboveBelowFrameType deps }
  end.

Definition mkCohReflAboveAboveFrameType {p k}
  (deps: DepsReflCohsSup p.+1 k): Type :=
  forall q r (Hq: q <= r) (Hr: r <= p)
    (d: FramePrev (RestrOfReflCohsSup deps))
    (c: PaintingPrev (RestrOfReflCohsSup deps) d),
  mkReflFrameAbove deps q (Hq ↕ (↑ Hr))
    (deps.(_depsReflCohsInf).(_reflFramesAbove).2 r Hr d c)
    (deps.(_reflPaintingsAbove).2 r Hr d c) =
  mkReflFrameAbove deps r.+1 (⇑ Hr)
    (deps.(_depsReflCohsInf).(_reflFramesAbove).2 q (Hq ↕ Hr) d c)
    (deps.(_reflPaintingsAbove).2 q (Hq ↕ Hr) d c).

Fixpoint mkCohReflAboveAboveFrameTypes {p}:
  forall {k} (deps: DepsReflCohsSup p k), Type :=
  match p with
  | 0 => fun _ _ => unit
  | S p =>
    fun k deps =>
    { _: mkCohReflAboveAboveFrameTypes deps.(1) &T
      mkCohReflAboveAboveFrameType deps }
  end.

Definition mkCohReflBelowBelowPaintingType {p k}
  (deps: DepsReflCohsSup p.+1 k)
  (extraDeps: DepsReflCohsSupExtension p.+1 k deps)
  (cohReflBelowBelowFrames:
    mkCohReflBelowBelowFrameTypes deps.(_depsReflCohsInf)): Type :=
  forall q r (Hq: q <= r) (Hr: r <= k)
    (d: FramePrev (RestrOfReflCohsInf deps.(_depsReflCohsInf)))
    (c: PaintingPrev (RestrOfReflCohsInf deps.(_depsReflCohsInf)) d),
  rew [PaintingBase
    (mkDepsRestr (CohsOfReflCohsInf deps.(_depsReflCohsInf).(1)))
    (mkExtraDeps (CohsExtOfReflCohsInf deps.(_depsReflCohsInf).(1)))]
    cohReflBelowBelowFrames.2 q r Hq Hr d in
  mkReflPaintingBelow deps.(1) (deps; extraDeps) q (Hq ↕ ↑ Hr)
    (deps.(_depsReflCohsInf).(_reflFramesBelow').2 r Hr d)
    (deps.(_depsReflCohsInf).(_reflPaintingsBelow).2 r Hr d c) =
  mkReflPaintingBelow deps.(1) (deps; extraDeps) r.+1 (⇑ Hr)
    (deps.(_depsReflCohsInf).(_reflFramesBelow').2 q (Hq ↕ Hr) d)
    (deps.(_depsReflCohsInf).(_reflPaintingsBelow).2 q (Hq ↕ Hr) d c).

Fixpoint mkCohReflBelowBelowPaintingTypes {p}:
  forall {k}
    (deps: DepsReflCohsSup p k)
    (extraDeps: DepsReflCohsSupExtension p k deps)
    (cohReflBelowBelowFrames:
      mkCohReflBelowBelowFrameTypes deps.(_depsReflCohsInf)), Type :=
  match p with
  | 0 => fun _ _ _ _ => unit
  | S p =>
    fun k deps extraDeps cohReflBelowBelowFrames =>
    { _: mkCohReflBelowBelowPaintingTypes deps.(1) (deps; extraDeps)
        cohReflBelowBelowFrames.1 &T
      mkCohReflBelowBelowPaintingType deps extraDeps cohReflBelowBelowFrames }
  end.

Definition mkCohReflAboveBelowPaintingType {p k}
  (deps: DepsReflCohsSup p.+1 k)
  (extraDeps: DepsReflCohsSupExtension p.+1 k deps)
  (cohReflAboveBelowFrames: mkCohReflAboveBelowFrameTypes deps): Type :=
  forall q r (Hq: q <= p) (Hr: r <= k)
    (d: FramePrev (RestrOfReflCohsSup deps))
    (c: PaintingPrev (RestrOfReflCohsSup deps) d),
  rew [mkPainting _] cohReflAboveBelowFrames.2 q r Hq Hr d c in
  mkReflPaintingAbove deps.(1) (deps; extraDeps) q Hq
    (deps.(_depsReflCohsInf).(_reflFramesBelow').2 r Hr d)
    (deps.(_depsReflCohsInf).(_reflPaintingsBelow).2 r Hr d c) =
  mkReflPaintingBelow deps extraDeps r Hr
    (deps.(_depsReflCohsInf).(_reflFramesAbove).2 q Hq d c)
    (deps.(_reflPaintingsAbove).2 q Hq d c).

Fixpoint mkCohReflAboveBelowPaintingTypes {p}:
  forall {k}
    (deps: DepsReflCohsSup p k)
    (extraDeps: DepsReflCohsSupExtension p k deps)
    (cohReflAboveBelowFrames: mkCohReflAboveBelowFrameTypes deps), Type :=
  match p with
  | 0 => fun _ _ _ _ => unit
  | S p =>
    fun k deps extraDeps cohReflAboveBelowFrames =>
    { _: mkCohReflAboveBelowPaintingTypes deps.(1) (deps; extraDeps)
        cohReflAboveBelowFrames.1 &T
      mkCohReflAboveBelowPaintingType deps extraDeps cohReflAboveBelowFrames }
  end.

Definition mkCohReflAboveAbovePaintingType {p k}
  (deps: DepsReflCohsSup p.+1 k)
  (extraDeps: DepsReflCohsSupExtension p.+1 k deps)
  (cohReflAboveAboveFrames: mkCohReflAboveAboveFrameTypes deps): Type :=
  forall q r (Hq: q <= r) (Hr: r <= p)
    (d: FramePrev (RestrOfReflCohsSup deps))
    (c: PaintingPrev (RestrOfReflCohsSup deps) d),
  rew [mkPainting _] cohReflAboveAboveFrames.2 q r Hq Hr d c in
  mkReflPaintingAbove deps extraDeps q (Hq ↕ ↑ Hr)
    (deps.(_depsReflCohsInf).(_reflFramesAbove).2 r Hr d c)
    (deps.(_reflPaintingsAbove).2 r Hr d c) =
  mkReflPaintingAbove deps extraDeps r.+1 (⇑ Hr)
    (deps.(_depsReflCohsInf).(_reflFramesAbove).2 q (Hq ↕ Hr) d c)
    (deps.(_reflPaintingsAbove).2 q (Hq ↕ Hr) d c).

Fixpoint mkCohReflAboveAbovePaintingTypes {p}:
  forall {k}
    (deps: DepsReflCohsSup p k)
    (extraDeps: DepsReflCohsSupExtension p k deps)
    (cohReflAboveAboveFrames: mkCohReflAboveAboveFrameTypes deps), Type :=
  match p with
  | 0 => fun _ _ _ _ => unit
  | S p =>
    fun k deps extraDeps cohReflAboveAboveFrames =>
    { _: mkCohReflAboveAbovePaintingTypes deps.(1) (deps; extraDeps)
        cohReflAboveAboveFrames.1 &T
      mkCohReflAboveAbovePaintingType deps extraDeps cohReflAboveAboveFrames }
  end.

Class DepsReflCohs2 p k := {
  _depsReflCohsSup: DepsReflCohsSup p k;
  _extraDepsCohs2: DepsCohs2Extension p k (Cohs2OfReflCohsSup _depsReflCohsSup);
  _extraDepsReflCohsSup: DepsReflCohsSupExtension p k _depsReflCohsSup;
  _cohReflRestrPaintingsBelowInf:
    mkCohReflRestrPaintingBelowInfTypes _depsReflCohsSup _extraDepsReflCohsSup;
  _cohReflRestrPaintingsBelowSup:
    mkCohReflRestrPaintingBelowSupTypes _depsReflCohsSup _extraDepsReflCohsSup;
  _cohReflRestrPaintingsAboveSup:
    mkCohReflRestrPaintingAboveSupTypes _depsReflCohsSup _extraDepsReflCohsSup;
  _cohReflBelowBelowFrames:
    mkCohReflBelowBelowFrameTypes _depsReflCohsSup.(_depsReflCohsInf);
  _cohReflBelowBelowPaintings:
    mkCohReflBelowBelowPaintingTypes
      _depsReflCohsSup _extraDepsReflCohsSup _cohReflBelowBelowFrames;
  _cohReflAboveBelowFrames:
    mkCohReflAboveBelowFrameTypes _depsReflCohsSup;
  _cohReflAboveBelowPaintings:
    mkCohReflAboveBelowPaintingTypes
      _depsReflCohsSup _extraDepsReflCohsSup _cohReflAboveBelowFrames;
  _cohReflAboveAboveFrames:
    mkCohReflAboveAboveFrameTypes _depsReflCohsSup;
  _cohReflAboveAbovePaintings:
    mkCohReflAboveAbovePaintingTypes
      _depsReflCohsSup _extraDepsReflCohsSup _cohReflAboveAboveFrames;
}.

#[local]
Instance proj1DepsReflCohs2 {p k} (depsCohs2: DepsReflCohs2 p.+1 k):
DepsReflCohs2 p k.+1 :=
{|
  _depsReflCohsSup := depsCohs2.(_depsReflCohsSup).(1);
  _extraDepsCohs2 := (Cohs2OfReflCohsSup depsCohs2.(_depsReflCohsSup);
    depsCohs2.(_extraDepsCohs2));
  _extraDepsReflCohsSup := (depsCohs2.(_depsReflCohsSup);
    depsCohs2.(_extraDepsReflCohsSup));
  _cohReflRestrPaintingsBelowInf :=
    depsCohs2.(_cohReflRestrPaintingsBelowInf).1;
  _cohReflRestrPaintingsBelowSup :=
    depsCohs2.(_cohReflRestrPaintingsBelowSup).1;
  _cohReflRestrPaintingsAboveSup :=
    depsCohs2.(_cohReflRestrPaintingsAboveSup).1;
  _cohReflBelowBelowFrames :=
    depsCohs2.(_cohReflBelowBelowFrames).1;
  _cohReflBelowBelowPaintings :=
    depsCohs2.(_cohReflBelowBelowPaintings).1;
  _cohReflAboveBelowFrames :=
    depsCohs2.(_cohReflAboveBelowFrames).1;
  _cohReflAboveBelowPaintings :=
    depsCohs2.(_cohReflAboveBelowPaintings).1;
  _cohReflAboveAboveFrames :=
    depsCohs2.(_cohReflAboveAboveFrames).1;
  _cohReflAboveAbovePaintings :=
    depsCohs2.(_cohReflAboveAbovePaintings).1;
|}.

Declare Scope depsreflcohs2_scope.
Delimit Scope depsreflcohs2_scope with depsreflcohs2.
Bind Scope depsreflcohs2_scope with DepsReflCohs2.
Notation "x .(1)" := (proj1DepsReflCohs2 x%depsreflcohs2)
  (at level 1, left associativity, format "x .(1)"): depsreflcohs2_scope.

Definition ReflBelowOfReflCohs2 {p k}
  (depsCohs2: DepsReflCohs2 p k): DepsReflBelow p k :=
  ReflBelowOfReflCohsSup depsCohs2.(_depsReflCohsSup).

Definition RestrOfReflCohs2 {p k}
  (depsCohs2: DepsReflCohs2 p k): DepsRestr p k :=
  RestrOfReflCohsSup depsCohs2.(_depsReflCohsSup).

Definition CohsOfReflCohs2 {p k}
  (depsCohs2: DepsReflCohs2 p k): DepsCohs p k :=
  CohsOfReflCohsSup depsCohs2.(_depsReflCohsSup).

Definition Cohs2OfReflCohs2 {p k}
  (depsCohs2: DepsReflCohs2 p k): DepsCohs2 p k :=
  Cohs2OfReflCohsSup depsCohs2.(_depsReflCohsSup).

Definition ReflCohsInfOfReflCohs2 {p k}
  (depsCohs2: DepsReflCohs2 p k): DepsReflCohsInf p k :=
  depsCohs2.(_depsReflCohsSup).(_depsReflCohsInf).

Definition RestrExtOfReflCohs2 {p k}
  (depsCohs2: DepsReflCohs2 p k): DepsRestrExtension p k
    (RestrOfReflCohs2 depsCohs2) :=
  RestrExtOfReflCohsSup depsCohs2.(_depsReflCohsSup).

Definition CohsExtOfReflCohs2 {p k}
  (depsCohs2: DepsReflCohs2 p k): DepsCohsExtension p k
    (CohsOfReflCohs2 depsCohs2) :=
  CohsExtOfReflCohsSup depsCohs2.(_depsReflCohsSup).

Definition mkCohReflRestrLayerBelowInf {p k}
  (deps: DepsReflCohs2 p.+1 k)
  (ε: arity) q r (Hq: q <= k) (Hr: r <= q)
  (d: mkFrame (mkDepsRestr (CohsOfReflCohs2 deps)).(1).(1))
  (l: mkLayer (mkDepsRestr (CohsOfReflCohs2 deps)).(1).(_restrFrames) d)
  (prevCohReflRestrFrames:
    mkCohReflRestrFrameBelowInfTypes
      (mkDepsCohs (Cohs2OfReflCohs2 deps).(1))
      (mkReflFramesBelow (ReflCohsInfOfReflCohs2 deps)).1
      (mkReflPaintingsBelow
        deps.(_depsReflCohsSup).(1)%depsreflcohssup
        (deps.(_depsReflCohsSup); deps.(_extraDepsReflCohsSup))%extradepsreflcohssup)):
  rew [mkLayer _] prevCohReflRestrFrames.2 q.+1 r.+1 (⇑ Hq) (⇑ Hr) ε d in
  mkReflLayerBelow
    (CohsOfReflCohs2 deps)
    (ReflCohsInfOfReflCohs2 deps).(_reflFramesBelow')
    (ReflCohsInfOfReflCohs2 deps).(_reflPaintingsBelow) _
    (ReflCohsInfOfReflCohs2 deps).(_cohReflRestrFramesBelowInf)
    q Hq _
    (mkRestrLayer
      (CohsOfReflCohs2 deps).(_restrPaintings)
      (CohsOfReflCohs2 deps).(_cohs)
      r (Hr ↕ Hq) ε d l) =
  mkRestrLayer
    (mkDepsCohs (Cohs2OfReflCohs2 deps)).(1).(_restrPaintings)
    (mkDepsCohs (Cohs2OfReflCohs2 deps)).(1).(_cohs) r (Hr ↕ ↑ Hq) ε _
    (mkReflLayerBelow
      (mkDepsCohs (Cohs2OfReflCohs2 deps).(1))
      (mkReflFramesBelow (ReflCohsInfOfReflCohs2 deps)).1
      (mkReflPaintingsBelow
        deps.(_depsReflCohsSup).(1)%depsreflcohssup
        (deps.(_depsReflCohsSup); deps.(_extraDepsReflCohsSup))%extradepsreflcohssup) _
      prevCohReflRestrFrames
      q.+1 (⇑ Hq) d l).
Proof.
  apply functional_extensionality_dep.
  intros θ.
  unfold mkRestrLayer, mkReflLayerBelow.
  rewrite <- map_subst_app, <- !map_subst.
  simpl.
  rewrite <- (deps.(_cohReflRestrPaintingsBelowInf).2 q r Hq Hr ε _ (l θ)).
  rewrite rew_map with
    (P := fun b => (mkDepsRestr (CohsOfReflCohs2 deps).(1)).(_paintings).2 b)
    (f := fun x => (mkDepsRestr (CohsOfReflCohs2 deps).(1)).(_restrFrames).2
      0 leR_O θ x).
  rewrite rew_map with
    (f := fun d1 => (ReflCohsInfOfReflCohs2 deps).(_reflFramesBelow').2 q Hq d1).
  rewrite rew_map with
    (P := fun b => (mkDepsCohs (Cohs2OfReflCohs2 deps)).(1).(
        _deps).(_paintings).2 b)
    (f := fun d0 => (mkDepsCohs (Cohs2OfReflCohs2 deps)).(1).(
      _deps).(_restrFrames).2 r (Hr ↕ ↑ Hq) ε d0).
  rewrite 4 rew_compose.
  apply rew_swap with
    (P := fun b => (mkDepsCohs (Cohs2OfReflCohs2 deps)).(1).(
      _deps).(_paintings).2 b).
  rewrite rew_app_rl. now trivial.
  now apply (mkFrame (RestrOfReflCohs2 deps).(1)).(UIP).
Defined.

Fixpoint mkCohReflRestrFramesBelowInf {p k} (deps: DepsReflCohs2 p k):
  mkCohReflRestrFrameBelowInfTypes
    (mkDepsCohs (Cohs2OfReflCohs2 deps))
    (mkReflFramesBelow (ReflCohsInfOfReflCohs2 deps))
    (mkReflPaintingsBelow deps.(_depsReflCohsSup) deps.(_extraDepsReflCohsSup)).
Proof.
  destruct p.
  - unshelve econstructor.
    + now exact tt.
    + now trivial.
  - set (h := mkCohReflRestrFramesBelowInf p k.+1 deps.(1)%depsreflcohs2).
    unshelve econstructor.
    + now exact h.
    + intros q r Hq Hr ε [l c].
      unshelve eapply eq_existT_curried.
      * now exact (h.2 q.+1 r.+1 (⇑ Hq) (⇑ Hr) ε l).
      * now exact (mkCohReflRestrLayerBelowInf deps ε q r Hq Hr l c h).
Defined.

Instance mkDepsReflCohsInf {p k} (deps: DepsReflCohs2 p k): DepsReflCohsInf p.+1 k.
Proof.
  unshelve econstructor.
  - unshelve econstructor.
    + now exact (mkDepsCohs (Cohs2OfReflCohs2 deps)).
    + now exact (mkExtraCohs deps.(_extraDepsCohs2)).
    + now apply mkCohPaintings.
  - now apply mkReflFramesBelow.
  - now exact (mkReflPaintingsBelow _ deps.(_extraDepsReflCohsSup)).
  - now apply mkIdRestrReflFramesBelow.
  - now apply mkReflFramesAbove.
  - now apply mkIdRestrReflPaintingsBelow. 
  - now apply mkCohReflRestrFramesBelowInf.
Defined.

Definition mkCohReflRestrLayerBelowSup {p k}
  (deps: DepsReflCohs2 p.+1 k)
  (ε: arity) q r (Hq: q <= r) (Hr: r <= k)
  (d: mkFrame (mkDepsRestr (CohsOfReflCohs2 deps)).(1).(1))
  (l: mkLayer (mkDepsRestr (CohsOfReflCohs2 deps)).(1).(_restrFrames) d)
  (prevCohReflRestrFrames:
    mkCohReflRestrFrameBelowSupTypes
      (mkDepsReflCohsInf deps.(1)%depsreflcohs2)):
  rew [mkLayer _] prevCohReflRestrFrames.2 q.+1 r.+1 (⇑ Hq) (⇑ Hr) ε d in
  mkReflLayerBelow
    (CohsOfReflCohs2 deps)
    (ReflCohsInfOfReflCohs2 deps).(_reflFramesBelow')
    (ReflCohsInfOfReflCohs2 deps).(_reflPaintingsBelow) _
    (ReflCohsInfOfReflCohs2 deps).(_cohReflRestrFramesBelowInf)
    q (Hq ↕ Hr) _
    (mkRestrLayer
      (CohsOfReflCohs2 deps).(_restrPaintings)
      (CohsOfReflCohs2 deps).(_cohs)
      r Hr ε d l) =
  mkRestrLayer
    (CohsOfReflCohsInf (mkDepsReflCohsInf deps).(1)).(_restrPaintings)
    (CohsOfReflCohsInf (mkDepsReflCohsInf deps).(1)).(_cohs)
    r.+1 (⇑ Hr) ε _
    (mkReflLayerBelow
      (CohsOfReflCohsInf (mkDepsReflCohsInf deps).(1))
      (mkDepsReflCohsInf deps).(1).(_reflFramesBelow')
      (mkDepsReflCohsInf deps).(1).(_reflPaintingsBelow) _
      (mkDepsReflCohsInf deps).(1).(_cohReflRestrFramesBelowInf)
      q (Hq ↕ ↑ Hr) d l).
Proof.
  apply functional_extensionality_dep.
  intros θ.
  unfold mkRestrLayer, mkReflLayerBelow.
  rewrite <- map_subst_app, <- !map_subst.

  set (d0 := mkRestrFrame (depsCohs := (CohsOfReflCohs2 deps).(1)) 0 leR_O θ d).

  set (h := deps.(_cohReflRestrPaintingsBelowSup).2 q r Hq Hr ε d0 (l θ)).
  simpl in h |- *; rewrite <- h; clear h.

  rewrite rew_map with
    (P := fun b => (mkDepsRestr (CohsOfReflCohs2 deps).(1)).(_paintings).2 b)
    (f := fun x => (mkDepsRestr (CohsOfReflCohs2 deps).(1)).(_restrFrames).2
      0 leR_O θ x).
  rewrite rew_map with
    (f := fun d1 =>
      (toDepsReflBelow
        (ReflCohsInfOfReflCohs2 deps).(_depsCohs2).(_depsCohs)
        (ReflCohsInfOfReflCohs2 deps).(_reflFramesBelow')).(_reflFramesBelow).2
        q (Hq ↕ Hr) d1).
  rewrite rew_map with
    (P := fun b =>
      (CohsOfReflCohsInf (mkDepsReflCohsInf deps).(1)).(_deps).(_paintings).2 b)
    (f := fun d1 =>
      (CohsOfReflCohsInf (mkDepsReflCohsInf deps).(1)).(_deps).(_restrFrames).2
        r.+1 (⇑ Hr) ε d1).
  rewrite 4 rew_compose.
  apply rew_swap with
    (P := fun b =>
      (CohsOfReflCohsInf (mkDepsReflCohsInf deps).(1)).(_deps).(_paintings).2 b).
  rewrite rew_app_rl. now trivial.
  now apply (mkFrame (RestrOfReflCohs2 deps).(1)).(UIP).
Defined.

Fixpoint mkCohReflRestrFramesBelowSup {p k} (deps: DepsReflCohs2 p k):
  mkCohReflRestrFrameBelowSupTypes (mkDepsReflCohsInf deps).
Proof.
  destruct p.
  - unshelve econstructor.
    + now exact tt.
    + now trivial.
  - set (h := mkCohReflRestrFramesBelowSup p k.+1 deps.(1)%depsreflcohs2).
    unshelve econstructor.
    + now exact h.
    + intros q r Hq Hr ε [l c].
      unshelve eapply eq_existT_curried.
      * now exact (h.2 q.+1 r.+1 (⇑ Hq) (⇑ Hr) ε l).
      * now exact (mkCohReflRestrLayerBelowSup deps ε q r Hq Hr l c h).
Defined.

Definition mkCohReflRestrLayerAboveSup {p k}
  (deps: DepsReflCohs2 p.+1 k)
  (ε: arity) q r (Hq: q <= p) (Hr: r <= k)
  (d: mkFrame ((RestrOfReflCohsInf (mkDepsReflCohsInf deps)).(1).(1)))
  (l: mkLayer (RestrOfReflCohsInf (mkDepsReflCohsInf deps)).(1).(_restrFrames) d)
  (c: mkPainting
        (mkDepsRestr (CohsOfReflCohs2 deps); mkExtraDeps (CohsExtOfReflCohs2 deps))
        (d; l))
  (prevCohReflRestrFrames:
    mkCohReflRestrFrameAboveSupTypes
      (mkDepsReflCohsInf deps.(1)%depsreflcohs2)
      (mkReflPaintingsAbove deps.(1).(_depsReflCohsSup)
        deps.(1).(_extraDepsReflCohsSup))):
  rew [mkLayer _] prevCohReflRestrFrames.2 q r.+1 Hq (⇑ Hr) ε d (l; c) in
  mkReflLayerAbove deps.(_depsReflCohsSup).(_depsReflCohsInf)
    deps.(_depsReflCohsSup).(_reflPaintingsAbove) _
    deps.(_depsReflCohsSup).(_cohReflRestrFramesAboveSup)
    q Hq
    ((CohsOfReflCohsInf (mkDepsReflCohsInf deps)).(_deps).(_restrFrames).2 r Hr ε (d; l)).1
    (((CohsOfReflCohsInf (mkDepsReflCohsInf deps)).(_deps).(_restrFrames).2 r Hr ε (d; l)).2;
     (CohsOfReflCohsInf (mkDepsReflCohsInf deps)).(_restrPaintings).2 r Hr ε (d; l) c) =
  mkRestrLayer
    (CohsOfReflCohsInf (mkDepsReflCohsInf deps)).(_restrPaintings)
    (CohsOfReflCohsInf (mkDepsReflCohsInf deps)).(_cohs)
    r Hr ε _
    (mkReflLayerAbove (mkDepsReflCohsInf deps).(1)
      (mkReflPaintingsAbove deps.(1).(_depsReflCohsSup) deps.(1).(_extraDepsReflCohsSup)) _
      prevCohReflRestrFrames q Hq d (l; c)).
Proof.
  apply functional_extensionality_dep.
  intros θ.
  unfold mkRestrLayer, mkReflLayerAbove.
  rewrite <- map_subst_app, <- !map_subst.

  set (d0 := (CohsOfReflCohsInf (mkDepsReflCohsInf deps).(1)).(_deps).(_restrFrames).2
    0 leR_O θ d).
  set (c0 := (CohsOfReflCohsInf (mkDepsReflCohsInf deps).(1)).(_restrPaintings).2
    0 leR_O θ d (l; c)).

  simpl.
  rewrite <- (deps.(_cohReflRestrPaintingsAboveSup).2 q r Hq Hr ε d0 c0).

  eassert (coh_pair_eq: (_;_) = (_;_)).
  { unshelve eapply eq_existT_curried.
    now exact ((CohsOfReflCohs2 deps).(_cohs).2 r Hr 0 leR_O ε θ d).
    now exact ((Cohs2OfReflCohs2 deps).(_cohPaintings).2 r Hr 0 leR_O ε θ d (l; c)). }
  rewrite <- (map_subst (P := fun _ => unit) (fun x _ =>
    deps.(_depsReflCohsSup).(_reflPaintingsAbove).2 q Hq x.1 x.2) coh_pair_eq tt).

  rewrite rew_map with
    (P := fun b =>
      (CohsOfReflCohsInf (mkDepsReflCohsInf deps)).(_deps).(_paintings).2 b)
    (f := fun x => (mkDepsRestr
      (CohsOfReflCohsInf deps.(_depsReflCohsSup).(_depsReflCohsInf))).(_restrFrames).2
      0 leR_O θ x).
  rewrite rew_map with
    (P := fun b =>
      (CohsOfReflCohsInf (mkDepsReflCohsInf deps)).(_deps).(_paintings).2 b)
    (f := fun d1 =>
      (CohsOfReflCohsInf (mkDepsReflCohsInf deps)).(_deps).(_restrFrames).2
        r Hr ε d1).
  rewrite rew_map with
    (P := fun x => mkPainting (RestrExtOfReflCohsSup deps.(_depsReflCohsSup)) x)
    (f := fun x =>
      (AboveOfReflCohsInf deps.(_depsReflCohsSup).(_depsReflCohsInf)).(_reflFramesAbove').2
        q Hq x.1 x.2).
  rewrite 4 rew_compose.
  apply rew_swap with
    (P := fun x => mkPainting (RestrExtOfReflCohsSup deps.(_depsReflCohsSup)) x).
  rewrite rew_app_rl. now trivial.
  now apply (mkFrame (RestrOfReflCohsSup deps.(_depsReflCohsSup))).(UIP).
Defined.

Definition mkCohReflRestrLayerAboveSup0 {p k}
  (deps: DepsReflCohs2 p k) r (Hr: r <= k) (ε: arity)
  (d: FrameBase (RestrOfReflCohsInf (mkDepsReflCohsInf deps)))
  (c: PaintingBase (RestrOfReflCohsInf (mkDepsReflCohsInf deps))
    (RestrExtOfReflCohsInf (mkDepsReflCohsInf deps)) d):
  rew [mkLayer _] (mkCohReflRestrFramesBelowSup deps).2 0 r leR_O Hr ε d in
  mkReflLayerAbove0 (ReflCohsInfOfReflCohs2 deps)
    (mkRestrFrames.2 r Hr ε d)
    (mkRestrPainting (CohsExtOfReflCohs2 deps) r Hr ε d c) =
  mkRestrLayer
    (mkDepsReflCohsInf deps).(_depsCohs2).(_depsCohs).(_restrPaintings)
    (mkDepsReflCohsInf deps).(_depsCohs2).(_depsCohs).(_cohs) r Hr ε
    (mkReflFrameAbove0 (mkDepsReflCohsInf deps).(1) d c).1
    (mkReflFrameAbove0 (mkDepsReflCohsInf deps).(1) d c).2.
Proof.
  apply functional_extensionality_dep; intro θ.
  unfold mkRestrLayer.
  rewrite <- map_subst_app, <- !map_subst.
  set (deps' := (CohsOfReflCohsInf (mkDepsReflCohsInf deps)).(_deps)).
  rewrite rew_map with
    (P := fun b => deps'.(_paintings).2 b)
    (f := fun x => deps'.(_restrFrames).2 0 leR_O θ x).
  rewrite rew_map with
    (P := fun b => deps'.(_paintings).2 b)
    (f := fun d0 => deps'.(_restrFrames).2 r Hr ε d0).
  rewrite 2 rew_compose.
  apply rew_swap with (P := fun b => deps'.(_paintings).2 b).
  rewrite rew_app_rl. now trivial.
  now apply (deps'.(_frames).2.(UIP)).
Defined.

Definition mkCohReflRestrFrameAboveSup {p k} (deps: DepsReflCohs2 p k)
  (cohPrefix:
    mkCohReflRestrFrameAboveSupTypes
      (mkDepsReflCohsInf deps).(1)
      (mkReflPaintingsAbove deps.(_depsReflCohsSup) deps.(_extraDepsReflCohsSup)).1):
  mkCohReflRestrFrameAboveSupType (mkDepsReflCohsInf deps) _ cohPrefix.
Proof.
  intros q r Hq Hr ε d c.
  destruct q.
  - unshelve eapply eq_existT_curried.
    + now exact ((mkCohReflRestrFramesBelowSup deps).2 0 r leR_O Hr ε d).
    + now exact (mkCohReflRestrLayerAboveSup0 deps r Hr ε d c).
  - destruct p; [now contradiction |].
    destruct d as [d l].
    unshelve eapply eq_existT_curried.
    + now exact (cohPrefix.2 q r.+1 Hq (⇑ Hr) ε d (l; c)).
    + now exact (mkCohReflRestrLayerAboveSup deps ε q r Hq Hr d l c cohPrefix).
Defined.

Fixpoint mkCohReflRestrFramesAboveSupPrefix {p k} (deps: DepsReflCohs2 p k):
  mkCohReflRestrFrameAboveSupTypes
    ((mkDepsReflCohsInf deps).(1))
    ((mkReflPaintingsAbove deps.(_depsReflCohsSup) deps.(_extraDepsReflCohsSup)).1).
Proof.
  destruct p.
  - now exact tt.
  - set (h := mkCohReflRestrFramesAboveSupPrefix p k.+1 deps.(1)%depsreflcohs2).
    unshelve econstructor.
    + now exact h.
    + now exact (mkCohReflRestrFrameAboveSup deps.(1) h).
Defined.

Definition mkCohReflRestrFramesAboveSup {p k} (deps: DepsReflCohs2 p k):
  mkCohReflRestrFrameAboveSupTypes
    (mkDepsReflCohsInf deps)
    (mkReflPaintingsAbove deps.(_depsReflCohsSup) deps.(_extraDepsReflCohsSup)).
Proof.
  set (h := mkCohReflRestrFramesAboveSupPrefix deps).
  unshelve econstructor.
  - now exact h.
  - now exact (mkCohReflRestrFrameAboveSup deps h).
Defined.

Instance mkDepsReflCohsSup {p k} (deps: DepsReflCohs2 p k): DepsReflCohsSup p.+1 k.
Proof.
  unshelve econstructor.
  - now exact (mkReflPaintingsAbove _ deps.(_extraDepsReflCohsSup)).
  - now apply mkCohReflRestrFramesBelowSup.
  - now apply mkCohReflRestrFramesAboveSup.
Defined.

Definition mkCohReflBelowBelowLayer {p k}
  (deps: DepsReflCohs2 p.+1 k)
  q r (Hq: q <= r) (Hr: r <= k)
  (d: mkFrame (RestrOfReflCohsInf (ReflCohsInfOfReflCohs2 deps).(1)))
  (l: mkLayer (RestrOfReflCohsInf (ReflCohsInfOfReflCohs2 deps)).(_restrFrames) d)
  (prevCohReflBelowBelowFrames:
    mkCohReflBelowBelowFrameTypes (mkDepsReflCohsInf deps.(1)%depsreflcohs2)):
  rew [mkLayer _] prevCohReflBelowBelowFrames.2 q.+1 r.+1 (⇑ Hq) (⇑ Hr) d in
  mkReflLayerBelow
    (CohsOfReflCohsInf (mkDepsReflCohsInf deps).(1))
    (mkDepsReflCohsInf deps).(1).(_reflFramesBelow')
    (mkDepsReflCohsInf deps).(1).(_reflPaintingsBelow) _
    (mkDepsReflCohsInf deps).(1).(_cohReflRestrFramesBelowInf)
    q (Hq ↕ ↑ Hr) _
    (mkReflLayerBelow
      (CohsOfReflCohsInf (ReflCohsInfOfReflCohs2 deps))
      (ReflCohsInfOfReflCohs2 deps).(_reflFramesBelow')
      (ReflCohsInfOfReflCohs2 deps).(_reflPaintingsBelow) _
      (ReflCohsInfOfReflCohs2 deps).(_cohReflRestrFramesBelowInf)
      r Hr d l) =
  mkReflLayerBelow
    (CohsOfReflCohsInf (mkDepsReflCohsInf deps).(1))
    (mkDepsReflCohsInf deps).(1).(_reflFramesBelow')
    (mkDepsReflCohsInf deps).(1).(_reflPaintingsBelow) _
    (mkDepsReflCohsInf deps).(1).(_cohReflRestrFramesBelowInf)
    r.+1 (⇑ Hr) _
    (mkReflLayerBelow
      (CohsOfReflCohsInf (ReflCohsInfOfReflCohs2 deps))
      (ReflCohsInfOfReflCohs2 deps).(_reflFramesBelow')
      (ReflCohsInfOfReflCohs2 deps).(_reflPaintingsBelow) _
      (ReflCohsInfOfReflCohs2 deps).(_cohReflRestrFramesBelowInf)
      q (Hq ↕ Hr) d l).
Proof.
  apply functional_extensionality_dep.
  intro θ.
  unfold mkReflLayerBelow.
  rewrite <- map_subst_app, <- !map_subst.
  set (d0 := (CohsOfReflCohsInf (ReflCohsInfOfReflCohs2 deps)).(_deps)
    .(_restrFrames).2 0 leR_O θ d).
  set (deps' := mkDepsRestr (CohsOfReflCohsInf (mkDepsReflCohsInf deps).(1))).
  set (deps'' := mkDepsReflCohsInf deps.(1)).
  simpl.
  rewrite <- (deps.(_cohReflBelowBelowPaintings).2 q r Hq Hr d0 (l θ)).
  rewrite rew_map with
    (P := fun b => deps'.(1).(_paintings).2 b)
    (f := fun x => deps'.(1).(_restrFrames).2 0 leR_O θ x).
  rewrite rew_map with
    (P := fun b => deps'.(1).(_paintings).2 b)
    (f := fun d0 => deps''.(_reflFramesBelow').2 q (Hq ↕ ↑ Hr) d0).
  rewrite rew_map with
    (P := fun b => deps'.(1).(_paintings).2 b)
    (f := fun d1 => deps''.(_reflFramesBelow').2 r.+1 (⇑ Hr) d1).
  rewrite 4 rew_compose.
  apply rew_swap with (P := fun b => deps'.(1).(_paintings).2 b).
  rewrite rew_app_rl. now trivial.
  now apply (deps'.(1).(_frames).2.(UIP)).
Defined.

Fixpoint mkCohReflBelowBelowFrames {p k} (deps: DepsReflCohs2 p k):
  mkCohReflBelowBelowFrameTypes (mkDepsReflCohsInf deps).
Proof.
  destruct p.
  - unshelve econstructor. now exact tt.
    now intros q r Hq Hr [].
  - set (h := mkCohReflBelowBelowFrames p k.+1 deps.(1)%depsreflcohs2).
    unshelve econstructor.
    + now exact h.
    + intros q r Hq Hr [d l].
      unshelve eapply eq_existT_curried.
      * now exact (h.2 q.+1 r.+1 (⇑ Hq) (⇑ Hr) d).
      * now exact (mkCohReflBelowBelowLayer deps q r Hq Hr d l h).
Defined.

Definition mkCohReflAboveBelowLayer {p k}
  (deps: DepsReflCohs2 p.+1 k)
  q r (Hq: q <= p) (Hr: r <= k)
  (d: mkFrame ((RestrOfReflCohs2 deps).(1)))
  (l: mkLayer
    (paintings := (RestrOfReflCohs2 deps).(_paintings))
    (RestrOfReflCohs2 deps).(_restrFrames) d)
  (c: PaintingPrev (RestrOfReflCohsSup (mkDepsReflCohsSup deps)) (d; l))
  (prevCohReflAboveBelowFrames:
    mkCohReflAboveBelowFrameTypes (mkDepsReflCohsSup deps.(1)%depsreflcohs2)):
  rew [mkLayer _] prevCohReflAboveBelowFrames.2 q r.+1 Hq (⇑ Hr) d (l; c) in
  mkReflLayerAbove (mkDepsReflCohsSup deps).(1).(_depsReflCohsInf)
    (mkDepsReflCohsSup deps).(1).(_reflPaintingsAbove) _
    (mkDepsReflCohsSup deps).(1).(_cohReflRestrFramesAboveSup) q Hq
    ((mkDepsReflCohsInf deps).(_reflFramesBelow').2 r Hr (d; l)).1
    (((mkDepsReflCohsInf deps).(_reflFramesBelow').2 r Hr (d; l)).2;
     (mkDepsReflCohsInf deps).(_reflPaintingsBelow).2 r Hr (d; l) c) =
  mkReflLayerBelow
    (mkDepsReflCohsInf deps).(_depsCohs2).(_depsCohs)
    (mkDepsReflCohsInf deps).(_reflFramesBelow')
    (mkDepsReflCohsInf deps).(_reflPaintingsBelow) _
    (mkDepsReflCohsInf deps).(_cohReflRestrFramesBelowInf)
    r Hr
    ((mkDepsReflCohsInf deps).(_reflFramesAbove).2 q.+1 (⇑ Hq) (d; l) c).1
    ((mkDepsReflCohsInf deps).(_reflFramesAbove).2 q.+1 (⇑ Hq) (d; l) c).2.
Proof.
  apply functional_extensionality_dep.
  intro θ.
  unfold mkReflLayerBelow, mkReflLayerAbove.
  rewrite <- map_subst_app.

  set (d0 := (RestrOfReflCohs2 deps).(_restrFrames).2 0 leR_O θ d).
  set (c0 := (CohsOfReflCohs2 deps).(_restrPaintings).2 0 leR_O θ d (l; c)).
  set (x0 := (
    (ReflCohsInfOfReflCohs2 deps).(_reflFramesBelow').2 r Hr d0;
    (ReflCohsInfOfReflCohs2 deps).(_reflPaintingsBelow).2 r Hr d0 c0)).

  eassert (coh_below_inf_pair_eq: (_;_) = (_;_)).
  { unshelve eapply eq_existT_curried.
    - now exact ((ReflCohsInfOfReflCohs2 deps).(_cohReflRestrFramesBelowInf).2 r 0 Hr leR_O θ d).
    - now exact (deps.(_cohReflRestrPaintingsBelowInf).2 r 0 Hr leR_O θ d (l; c)). }
  rewrite <- (map_subst (P := fun _ => unit) (fun x _ =>
    (mkDepsReflCohsSup deps).(1).(_reflPaintingsAbove).2 q Hq x.1 x.2)
    coh_below_inf_pair_eq tt).

  rewrite (proj2 (@rew_swap _ _ _ _ (deps.(_cohReflAboveBelowFrames).2 q r Hq Hr d0 c0)
    ((mkDepsReflCohsSup deps).(1).(_reflPaintingsAbove).2 q Hq x0.1 x0.2) _)
    (deps.(_cohReflAboveBelowPaintings).2 q r Hq Hr d0 c0)).

  eassert (coh_above_sup_pair_eq: (_;_) = (_;_)).
  { unshelve eapply eq_existT_curried.
    - now exact (deps.(_depsReflCohsSup).(_cohReflRestrFramesAboveSup).2 q 0 Hq leR_O θ d (l; c)).
    - now exact (deps.(_cohReflRestrPaintingsAboveSup).2 q 0 Hq leR_O θ d (l; c)). }
  rewrite <- (map_subst (P := fun _ => unit) (fun x _ =>
    (mkDepsReflCohsInf deps).(_reflPaintingsBelow).2 r Hr x.1 x.2)
    coh_above_sup_pair_eq tt).

  rewrite rew_map with
    (P := fun b => mkPainting
      (RestrExtOfReflCohsInf (mkDepsReflCohsSup deps).(1).(_depsReflCohsInf)) b)
    (f := fun x => (mkDepsRestr (CohsOfReflCohsInf
      (mkDepsReflCohsSup deps).(1).(_depsReflCohsInf))).(_restrFrames).2 0 leR_O θ x).
  rewrite rew_map with
    (P := fun x => mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps).(1)) x)
    (f := fun x =>
      (mkDepsReflCohsSup deps).(1).(_depsReflCohsInf).(_reflFramesAbove).2 q Hq x.1 x.2).
  rewrite rew_map with
    (P := fun b => (mkDepsRestr
      (mkDepsReflCohsInf deps).(_depsCohs2).(_depsCohs).(1)).(_paintings).2 b)
    (f := fun x => (mkDepsReflCohsInf deps).(_reflFramesBelow').2 r Hr x.1).

  rewrite 4 rew_compose.

  apply rew_swap with (P := fun b => (mkDepsRestr (CohsOfReflCohsInf
    (mkDepsReflCohsSup deps).(1).(_depsReflCohsInf))).(_paintings).2 b).
  rewrite rew_app_rl. now trivial.
  now apply ((mkDepsRestr (CohsOfReflCohsInf
    (mkDepsReflCohsSup deps).(1).(_depsReflCohsInf))).(_frames).2.(UIP)).
Defined.

Definition mkCohReflAboveBelowLayer0 {p k}
  (deps: DepsReflCohs2 p k) r (Hr: r <= k)
  (d: FramePrev (RestrOfReflCohsSup (mkDepsReflCohsSup deps)))
  (c: PaintingPrev (RestrOfReflCohsSup (mkDepsReflCohsSup deps)) d):
  rew [mkLayer _] (mkCohReflBelowBelowFrames deps).2 0 r leR_O Hr d in
  mkReflLayerAbove0
    (mkDepsReflCohsInf deps).(1)
    ((mkReflFramesBelow (ReflCohsInfOfReflCohs2 deps)).2 r Hr d)
    (mkReflPaintingBelow deps.(_depsReflCohsSup) deps.(_extraDepsReflCohsSup) r Hr d c) =
  mkReflLayerBelow
    (mkDepsReflCohsInf deps).(_depsCohs2).(_depsCohs)
    (mkDepsReflCohsInf deps).(_reflFramesBelow')
    (mkDepsReflCohsInf deps).(_reflPaintingsBelow) _
    (mkDepsReflCohsInf deps).(_cohReflRestrFramesBelowInf) r Hr
    ((mkDepsReflCohsInf deps).(_reflFramesAbove).2 0 leR_O d c).1
    ((mkDepsReflCohsInf deps).(_reflFramesAbove).2 0 leR_O d c).2.
Proof.
  apply functional_extensionality_dep; intro θ.
  unfold mkReflLayerBelow.
  rewrite <- map_subst_app, <- !map_subst.
  set (deps' := mkDepsRestr (CohsOfReflCohsSup (mkDepsReflCohsSup deps).(1))).
  rewrite rew_map with
    (P := fun b => deps'.(_paintings).2 b)
    (f := fun x => deps'.(_restrFrames).2 0 leR_O θ x).
  rewrite rew_map with
    (P := fun b => deps'.(_paintings).2 b)
    (f := fun d0 => (mkDepsReflCohsInf deps).(_reflFramesBelow').2 r Hr d0).
  rewrite 2 rew_compose.
  apply rew_swap with (P := fun b => deps'.(_paintings).2 b).
  rewrite rew_app_rl. now trivial.
  now apply (deps'.(_frames).2.(UIP)).
Defined.

Definition mkCohReflAboveBelowFrame {p k} (deps: DepsReflCohs2 p k)
  (cohPrefix: mkCohReflAboveBelowFrameTypes (mkDepsReflCohsSup deps).(1)):
  mkCohReflAboveBelowFrameType (mkDepsReflCohsSup deps).
Proof.
  intros q r Hq Hr d c.
  destruct q.
  - unshelve eapply eq_existT_curried.
    + now exact ((mkCohReflBelowBelowFrames deps).2 0 r leR_O Hr d).
    + now exact (mkCohReflAboveBelowLayer0 deps r Hr d c).
  - destruct p; [now contradiction |].
    destruct d as [d l].
    unshelve eapply eq_existT_curried.
    + now exact (cohPrefix.2 q r.+1 Hq (⇑ Hr) d (l; c)).
    + now exact (mkCohReflAboveBelowLayer deps q r Hq Hr d l c cohPrefix).
Defined.

Fixpoint mkCohReflAboveBelowFramesPrefix {p k} (deps: DepsReflCohs2 p k):
  mkCohReflAboveBelowFrameTypes (mkDepsReflCohsSup deps).(1).
Proof.
  destruct p.
  - now exact tt.
  - set (h := mkCohReflAboveBelowFramesPrefix p k.+1 deps.(1)%depsreflcohs2).
    unshelve econstructor.
    + now exact h.
    + now exact (mkCohReflAboveBelowFrame deps.(1) h).
Defined.

Definition mkCohReflAboveBelowFrames {p k} (deps: DepsReflCohs2 p k):
  mkCohReflAboveBelowFrameTypes (mkDepsReflCohsSup deps).
Proof.
  set (h := mkCohReflAboveBelowFramesPrefix deps).
  unshelve econstructor.
  - now exact h.
  - now exact (mkCohReflAboveBelowFrame deps h).
Defined.

Definition mkCohReflAboveAboveLayer {p k}
  (deps: DepsReflCohs2 p.+1 k)
  q r (Hq: q <= r) (Hr: r <= p)
  (d: mkFrame ((RestrOfReflCohs2 deps).(1)))
  (l: mkLayer
    (paintings := (RestrOfReflCohs2 deps).(_paintings))
    (RestrOfReflCohs2 deps).(_restrFrames) d)
  (c: PaintingPrev (RestrOfReflCohsSup (mkDepsReflCohsSup deps)) (d; l))
  (prevCohReflAboveAboveFrames:
    mkCohReflAboveAboveFrameTypes (mkDepsReflCohsSup deps.(1)%depsreflcohs2)):
  rew [mkLayer _] prevCohReflAboveAboveFrames.2 q r Hq Hr d (l; c) in
  mkReflLayerAbove (mkDepsReflCohsInf deps)
    (mkDepsReflCohsSup deps).(_reflPaintingsAbove) _
    (mkDepsReflCohsSup deps).(_cohReflRestrFramesAboveSup) q (Hq ↕ ↑ Hr)
    ((mkDepsReflCohsInf deps).(_reflFramesAbove).2 r.+1 (⇑ Hr) (d; l) c).1
    (((mkDepsReflCohsInf deps).(_reflFramesAbove).2 r.+1 (⇑ Hr) (d; l) c).2;
     (mkDepsReflCohsSup deps).(_reflPaintingsAbove).2 r.+1 (⇑ Hr) (d; l) c) =
  mkReflLayerAbove (mkDepsReflCohsInf deps)
    (mkDepsReflCohsSup deps).(_reflPaintingsAbove) _
    (mkDepsReflCohsSup deps).(_cohReflRestrFramesAboveSup) r.+1 (⇑ Hr)
    ((mkDepsReflCohsInf deps).(_reflFramesAbove).2 q.+1 (⇑ (Hq ↕ Hr)) (d; l) c).1
    (((mkDepsReflCohsInf deps).(_reflFramesAbove).2 q.+1 (⇑ (Hq ↕ Hr)) (d; l) c).2;
     (mkDepsReflCohsSup deps).(_reflPaintingsAbove).2 q.+1 (⇑ (Hq ↕ Hr)) (d; l) c).
Proof.
  apply functional_extensionality_dep.
  intro θ.
  unfold mkReflLayerAbove.
  rewrite <- map_subst_app.

  set (d0 := (RestrOfReflCohs2 deps).(_restrFrames).2 0 leR_O θ d).
  set (c0 := (CohsOfReflCohs2 deps).(_restrPaintings).2 0 leR_O θ d (l; c)).

  eassert (coh_above_sup_r_pair_eq: (_;_) = (_;_)).
  { unshelve eapply eq_existT_curried.
    - now exact (deps.(_depsReflCohsSup).(_cohReflRestrFramesAboveSup).2 r 0 Hr leR_O θ d (l; c)).
    - now exact (deps.(_cohReflRestrPaintingsAboveSup).2 r 0 Hr leR_O θ d (l; c)). }
  rewrite <- (map_subst (P := fun _ => unit) (fun x _ =>
    (mkDepsReflCohsSup deps).(_reflPaintingsAbove).2 q (Hq ↕ ↑ Hr) x.1 x.2)
    coh_above_sup_r_pair_eq tt).

  eassert (coh_above_sup_q_pair_eq: (_;_) = (_;_)).
  { unshelve eapply eq_existT_curried.
    - now exact (deps.(_depsReflCohsSup).(_cohReflRestrFramesAboveSup).2 q 0 (Hq ↕ Hr) leR_O θ d (l; c)).
    - now exact (deps.(_cohReflRestrPaintingsAboveSup).2 q 0 (Hq ↕ Hr) leR_O θ d (l; c)). }
  rewrite <- (map_subst (P := fun _ => unit) (fun x _ =>
    (mkDepsReflCohsSup deps).(_reflPaintingsAbove).2 r.+1 (⇑ Hr) x.1 x.2)
    coh_above_sup_q_pair_eq tt).

  rewrite (proj2 (@rew_swap _ _ _ _ (deps.(_cohReflAboveAboveFrames).2 q r Hq Hr d0 c0)
    ((mkDepsReflCohsSup deps).(_reflPaintingsAbove).2 q (Hq ↕ ↑ Hr) _ _) _)
    (deps.(_cohReflAboveAbovePaintings).2 q r Hq Hr d0 c0)).

  set (deps' := mkDepsRestr (CohsOfReflCohsInf (mkDepsReflCohsInf deps))).
  set (deps'' := RestrExtOfReflCohsInf (mkDepsReflCohsInf deps)).
  rewrite rew_map with
    (P := fun b => deps'.(_paintings).2 b)
    (f := fun x => deps'.(_restrFrames).2 0 leR_O θ x).
  rewrite rew_map with
    (P := fun x => mkPainting deps'' x)
    (f := fun x => (mkDepsReflCohsInf deps).(_reflFramesAbove).2 q (Hq ↕ ↑ Hr) x.1 x.2).
  rewrite rew_map with
    (P := fun x => mkPainting deps'' x)
    (f := fun x => (mkDepsReflCohsInf deps).(_reflFramesAbove).2 r.+1 (⇑ Hr) x.1 x.2).
  rewrite 4 rew_compose.
  apply rew_swap with (P := fun x => mkPainting deps'' x).
  rewrite rew_app_rl. now trivial.
  now apply (mkFrame (RestrOfReflCohsInf (mkDepsReflCohsInf deps))).(UIP).
Defined.

Definition mkCohReflAboveAboveLayer0 {p k}
  (deps: DepsReflCohs2 p k) r (Hr: r <= p)
  (d: FramePrev (RestrOfReflCohsSup (mkDepsReflCohsSup deps)))
  (c: PaintingPrev (RestrOfReflCohsSup (mkDepsReflCohsSup deps)) d):
  rew <- [mkLayer _] ((mkCohReflAboveBelowFrames deps).2 r 0 Hr leR_O d c) in
  mkReflLayerAbove0
    (mkDepsReflCohsInf deps)
    ((mkDepsReflCohsInf deps).(_reflFramesAbove).2 r Hr d c)
    ((mkDepsReflCohsSup deps).(_reflPaintingsAbove).2 r Hr d c) =
  mkReflLayerAbove
    (mkDepsReflCohsSup deps).(_depsReflCohsInf)
    (mkDepsReflCohsSup deps).(_reflPaintingsAbove) _
    (mkDepsReflCohsSup deps).(_cohReflRestrFramesAboveSup) r Hr
    ((mkDepsReflCohsInf deps).(_reflFramesAbove).2 0 leR_O d c).1
    (((mkDepsReflCohsInf deps).(_reflFramesAbove).2 0 leR_O d c).2;
     (mkDepsReflCohsSup deps).(_reflPaintingsAbove).2 0 leR_O d c).
Proof.
  set (deps' := mkDepsRestr (CohsOfReflCohsSup (mkDepsReflCohsSup deps))).
  apply functional_extensionality_dep; intro θ.
  unfold mkReflLayerAbove, mkReflLayerAbove0.
  unfold eq_rect_r; cbn.
  rewrite <- map_subst_app.
  eassert (coh_id_pair_eq: (_;_) = (_;_)).
  { unshelve eapply eq_existT_curried.
    - now exact (mkIdRestrReflFrameBelow (ReflCohsInfOfReflCohs2 deps) 0 leR_O θ d).
    - now exact (mkIdRestrReflPaintingBelow deps.(_depsReflCohsSup)
        deps.(_extraDepsReflCohsSup) 0 leR_O θ d c). }
  rewrite <- (map_subst (P := fun _ => unit) (fun x _ => mkReflPaintingAbove
    deps.(_depsReflCohsSup) deps.(_extraDepsReflCohsSup)
    r Hr x.1 x.2) coh_id_pair_eq tt).
  rewrite rew_map with
    (P := fun b => deps'.(_paintings).2 b)
    (f := fun x => deps'.(_restrFrames).2 0 leR_O θ x).
  rewrite rew_map with
    (P := fun b => deps'.(_paintings).2 b)
    (f := fun x => (mkReflFramesAbove deps.(_depsReflCohsSup)).2 r Hr x.1 x.2).
  rewrite 2 rew_compose.
  apply rew_swap with (P := fun b => deps'.(_paintings).2 b).
  rewrite rew_app_rl. now trivial.
  now apply (deps'.(_frames).2.(UIP)).
Defined.

Definition mkCohReflAboveAboveFrame {p k} (deps: DepsReflCohs2 p k)
  (cohPrefix: mkCohReflAboveAboveFrameTypes (mkDepsReflCohsSup deps).(1)):
  mkCohReflAboveAboveFrameType (mkDepsReflCohsSup deps).
Proof.
  intros q r Hq Hr d c.
  destruct q.
  - unshelve eapply eq_existT_curried.
    + symmetry.
      now exact ((mkCohReflAboveBelowFrames deps).2 r 0 Hr leR_O d c).
    + now exact (mkCohReflAboveAboveLayer0 deps r Hr d c).
  - destruct r; [now contradiction |].
    destruct p; [now contradiction |].
    destruct d as [d l].
    unshelve eapply eq_existT_curried.
    + now exact (cohPrefix.2 q r Hq Hr d (l; c)).
    + now exact (mkCohReflAboveAboveLayer deps q r (⇓ Hq) (⇓ Hr) d l c cohPrefix).
Defined.

Fixpoint mkCohReflAboveAboveFramesPrefix {p k} (deps: DepsReflCohs2 p k):
  mkCohReflAboveAboveFrameTypes (mkDepsReflCohsSup deps).(1).
Proof.
  destruct p.
  - now exact tt.
  - set (h := mkCohReflAboveAboveFramesPrefix p k.+1 deps.(1)%depsreflcohs2).
    unshelve econstructor.
    + now exact h.
    + now exact (mkCohReflAboveAboveFrame deps.(1) h).
Defined.

Definition mkCohReflAboveAboveFrames {p k} (deps: DepsReflCohs2 p k):
  mkCohReflAboveAboveFrameTypes (mkDepsReflCohsSup deps).
Proof.
  set (h := mkCohReflAboveAboveFramesPrefix deps).
  unshelve econstructor.
  - now exact h.
  - now exact (mkCohReflAboveAboveFrame deps h).
Defined.

Definition cohReflAboveAboveL {p} (deps: DepsReflCohs2 p 0)
  (L: HasRefl
    (mkDepsReflCohsSup deps)
    (mkPainting (mkExtraDeps (CohsExtOfReflCohsInf (mkDepsReflCohsInf deps))))): Type :=
  mkCohReflAboveAbovePaintingType
    (mkDepsReflCohsSup deps)
    (TopReflCohSupDep L)
    (mkCohReflAboveAboveFrames deps).

(*
  L q (Hq ↕ ↑ Hr)
    ((mkReflFramesAbove _depsReflCohsSup).2 r Hr d c)
    (L' r Hr d c) =
  L r.+1 (⇑ Hr)
    ((mkReflFramesAbove _depsReflCohsSup).2 q (Hq ↕ Hr) d c)
    (L' q (Hq ↕ Hr) d c)
*)

Inductive DepsReflCohs2Extension p: forall k (deps: DepsReflCohs2 p k), Type :=
| TopReflCoh2Dep {deps: DepsReflCohs2 p 0}
  (L: HasRefl
    (mkDepsReflCohsSup deps)
    (mkPainting (mkExtraDeps (CohsExtOfReflCohsInf (mkDepsReflCohsInf deps)))))
  (cohL: cohReflAboveAboveL deps L):
  DepsReflCohs2Extension p 0 deps
| AddReflCoh2Dep {k} (deps: DepsReflCohs2 p.+1 k):
  DepsReflCohs2Extension p.+1 k deps -> DepsReflCohs2Extension p k.+1 deps.(1)%depsreflcohs2.

Arguments TopReflCoh2Dep {p deps}.
Arguments AddReflCoh2Dep {p k}.

Declare Scope extra_depsreflcohs2_scope.
Delimit Scope extra_depsreflcohs2_scope with extradepsreflcohs2.
Bind Scope extra_depsreflcohs2_scope with DepsReflCohs2Extension.
Notation "( x ; y )" := (AddReflCoh2Dep x y)
  (at level 0, format "( x ; y )"): extra_depsreflcohs2_scope.

Fixpoint mkExtraDepsReflCohsSup {p k} (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  DepsReflCohsSupExtension p.+1 k (mkDepsReflCohsSup deps).
Proof.
  destruct extraDeps.
  - now apply TopReflCohSupDep.
  - apply (AddReflCohSupDep (mkDepsReflCohsSup deps)).
    now exact (mkExtraDepsReflCohsSup p.+1 k deps extraDeps).
Defined.

Fixpoint mkCohReflRestrPaintingBelowInf {p k}
  (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkCohReflRestrPaintingBelowInfType
    (mkDepsReflCohsSup deps)
    (mkExtraDepsReflCohsSup deps extraDeps).
Proof.
  intros q r Hq Hr ε d [l c].
  destruct r.
  - now trivial.
  - destruct q; [now contradiction |].
    destruct extraDeps; [now contradiction |].
    unshelve eapply (eq_existT_curried_dep
      (Q := mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps.(1))))).
    + now exact (mkCohReflRestrLayerBelowInf deps ε q r (⇓ Hq) (⇓ Hr) d l
        (mkCohReflRestrFramesBelowInf deps.(1))).
    + now exact (mkCohReflRestrPaintingBelowInf p.+1 k deps extraDeps
        q r Hq Hr ε (d; l) c).
Defined.

Fixpoint mkCohReflRestrPaintingsBelowInf {p k}
  (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkCohReflRestrPaintingBelowInfTypes
    (mkDepsReflCohsSup deps)
    (mkExtraDepsReflCohsSup deps extraDeps).
Proof.
  destruct p.
  - unshelve econstructor. now exact tt.
    now apply mkCohReflRestrPaintingBelowInf.
  - unshelve econstructor.
    + now exact (mkCohReflRestrPaintingsBelowInf p k.+1
        deps.(1)%depsreflcohs2 (deps; extraDeps)%extradepsreflcohs2).
    + now apply mkCohReflRestrPaintingBelowInf.
Defined.

Fixpoint mkCohReflRestrPaintingAboveSup {p k}
  (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkCohReflRestrPaintingAboveSupType
    (mkDepsReflCohsSup deps)
    (mkExtraDepsReflCohsSup deps extraDeps).
Proof.
  intros q r Hq Hr ε d [l c].
  destruct r.
  - now trivial.
  - destruct extraDeps; [now contradiction |].
    unshelve eapply (eq_existT_curried_dep
      (Q := mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps)))).
    + now exact (mkCohReflRestrLayerAboveSup deps ε q r Hq Hr d l c
        (mkCohReflRestrFramesAboveSup deps.(1))).
    + now exact (mkCohReflRestrPaintingAboveSup p.+1 k deps extraDeps
        q.+1 r (⇑ Hq) Hr ε (d; l) c).
Defined.

Fixpoint mkCohReflRestrPaintingsAboveSup {p k}
  (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkCohReflRestrPaintingAboveSupTypes
    (mkDepsReflCohsSup deps)
    (mkExtraDepsReflCohsSup deps extraDeps).
Proof.
  destruct p.
  - unshelve econstructor. now exact tt.
    now apply mkCohReflRestrPaintingAboveSup.
  - unshelve econstructor.
    + now exact (mkCohReflRestrPaintingsAboveSup p k.+1
        deps.(1)%depsreflcohs2 (deps; extraDeps)%extradepsreflcohs2).
    + now apply mkCohReflRestrPaintingAboveSup.
Defined.

Fixpoint mkCohReflRestrPaintingBelowSup {p k}
  (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkCohReflRestrPaintingBelowSupType
    (mkDepsReflCohsSup deps)
    (mkExtraDepsReflCohsSup deps extraDeps).
Proof.
  intros q r Hq Hr ε d [l c].
  destruct q.
  - unshelve eapply (eq_existT_curried_dep
      (Q := mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps)))).
    + now exact (mkCohReflRestrLayerAboveSup0 deps r Hr ε d (l; c)).
    + now exact (mkCohReflRestrPaintingAboveSup deps extraDeps 0 r leR_O Hr ε d (l; c)).
  - destruct r; [now contradiction |].
    destruct extraDeps; [now contradiction |].
    unshelve eapply (eq_existT_curried_dep
      (Q := mkPainting (RestrExtOfReflCohsSup (mkDepsReflCohsSup deps.(1))))).
    + now exact (mkCohReflRestrLayerBelowSup deps ε q r (⇓ Hq) (⇓ Hr) d l
        (mkCohReflRestrFramesBelowSup deps.(1))).
    + now exact (mkCohReflRestrPaintingBelowSup p.+1 k deps extraDeps
        q r Hq Hr ε (d; l) c).
Defined.

Fixpoint mkCohReflRestrPaintingsBelowSup {p k}
  (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkCohReflRestrPaintingBelowSupTypes
    (mkDepsReflCohsSup deps)
    (mkExtraDepsReflCohsSup deps extraDeps).
Proof.
  destruct p.
  - unshelve econstructor. now exact tt.
    now apply mkCohReflRestrPaintingBelowSup.
  - unshelve econstructor.
    + now exact (mkCohReflRestrPaintingsBelowSup p k.+1
        deps.(1)%depsreflcohs2 (deps; extraDeps)%extradepsreflcohs2).
    + now apply mkCohReflRestrPaintingBelowSup.
Defined.

Fixpoint mkCohReflAboveAbovePainting {p k} (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkCohReflAboveAbovePaintingType
    (mkDepsReflCohsSup deps)
    (mkExtraDepsReflCohsSup deps extraDeps)
    (mkCohReflAboveAboveFrames deps).
Proof.
  intros q r Hq Hr d c.
  destruct extraDeps.
  - now apply cohL.
  - destruct c as [l c].
    unshelve eapply (eq_existT_curried_dep (Q := mkPainting
      (mkExtraDeps (CohsExtOfReflCohsSup (mkDepsReflCohsSup deps))))).
    + now exact (mkCohReflAboveAboveLayer deps q r Hq Hr d l c
        (mkCohReflAboveAboveFrames deps.(1)%depsreflcohs2)).
    + now exact (mkCohReflAboveAbovePainting p.+1 k deps extraDeps
        q.+1 r.+1 (⇑ Hq) (⇑ Hr) (d; l) c).
Defined.

Fixpoint mkCohReflAboveAbovePaintings {p k}
  (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkCohReflAboveAbovePaintingTypes
    (mkDepsReflCohsSup deps)
    (mkExtraDepsReflCohsSup deps extraDeps)
    (mkCohReflAboveAboveFrames deps).
Proof.
  destruct p.
  - unshelve econstructor. now exact tt.
    now apply mkCohReflAboveAbovePainting.
  - unshelve econstructor.
    + now exact (mkCohReflAboveAbovePaintings p k.+1
        deps.(1)%depsreflcohs2 (deps; extraDeps)%extradepsreflcohs2).
    + now apply mkCohReflAboveAbovePainting.
Defined.

Fixpoint mkCohReflAboveBelowPainting {p k} (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkCohReflAboveBelowPaintingType
    (mkDepsReflCohsSup deps)
    (mkExtraDepsReflCohsSup deps extraDeps)
    (mkCohReflAboveBelowFrames deps).
Proof.
  intros q r Hq Hr d c.
  destruct r.
  - apply rew_swap with (P := mkPainting _), eq_sym.
    unshelve eapply (eq_existT_curried_dep (Q := mkPainting
      (mkExtraDeps (CohsExtOfReflCohsSup (mkDepsReflCohsSup deps))))).
    + now exact (mkCohReflAboveAboveLayer0 deps q Hq d c).
    + now exact (mkCohReflAboveAbovePainting deps extraDeps 0 q leR_O Hq d c).
  - destruct extraDeps; [now contradiction |].
    destruct c as [l c].
    unshelve eapply (eq_existT_curried_dep (Q := mkPainting
      (mkExtraDeps (CohsExtOfReflCohsSup (mkDepsReflCohsSup deps.(1)))))).
    + now exact (mkCohReflAboveBelowLayer deps q r Hq Hr d l c
        (mkCohReflAboveBelowFrames deps.(1)%depsreflcohs2)).
    + now exact (mkCohReflAboveBelowPainting p.+1 k deps extraDeps
        q.+1 r Hq Hr (d; l) c).
Defined.

Fixpoint mkCohReflAboveBelowPaintings {p k}
  (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkCohReflAboveBelowPaintingTypes
    (mkDepsReflCohsSup deps)
    (mkExtraDepsReflCohsSup deps extraDeps)
    (mkCohReflAboveBelowFrames deps).
Proof.
  destruct p.
  - unshelve econstructor. now exact tt.
    now apply mkCohReflAboveBelowPainting.
  - unshelve econstructor.
    + now exact (mkCohReflAboveBelowPaintings p k.+1
        deps.(1)%depsreflcohs2 (deps; extraDeps)%extradepsreflcohs2).
    + now apply mkCohReflAboveBelowPainting.
Defined.

Fixpoint mkCohReflBelowBelowPainting {p k} (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkCohReflBelowBelowPaintingType
    (mkDepsReflCohsSup deps)
    (mkExtraDepsReflCohsSup deps extraDeps)
    (mkCohReflBelowBelowFrames deps).
Proof.
  intros q r Hq Hr d c.
  destruct q.
  - unshelve eapply (eq_existT_curried_dep (Q := mkPainting
      (mkExtraDeps (CohsExtOfReflCohsSup (mkDepsReflCohsSup deps).(1))))).
    + now exact (mkCohReflAboveBelowLayer0 deps r Hr d c).
    + now exact (mkCohReflAboveBelowPainting deps extraDeps 0 r leR_O Hr d c).
  - destruct r; [now contradiction |].
    destruct extraDeps; [now contradiction |].
    destruct c as [l c].
    unshelve eapply (eq_existT_curried_dep (Q := mkPainting
      (mkExtraDeps (CohsExtOfReflCohsSup (mkDepsReflCohsSup deps.(1)).(1))))).
    + now exact (mkCohReflBelowBelowLayer deps q r Hq Hr d l
        (mkCohReflBelowBelowFrames deps.(1)%depsreflcohs2)).
    + now exact (mkCohReflBelowBelowPainting p.+1 k deps extraDeps
        q r Hq Hr (d; l) c).
Defined.

Fixpoint mkCohReflBelowBelowPaintings {p k}
  (deps: DepsReflCohs2 p k)
  (extraDeps: DepsReflCohs2Extension p k deps):
  mkCohReflBelowBelowPaintingTypes
    (mkDepsReflCohsSup deps)
    (mkExtraDepsReflCohsSup deps extraDeps)
    (mkCohReflBelowBelowFrames deps).
Proof.
  destruct p.
  - unshelve econstructor. now exact tt.
    now apply mkCohReflBelowBelowPainting.
  - unshelve econstructor.
    + now exact (mkCohReflBelowBelowPaintings p k.+1
        deps.(1)%depsreflcohs2 (deps; extraDeps)%extradepsreflcohs2).
    + now apply mkCohReflBelowBelowPainting.
Defined.

Definition dgnDepsRestr {p} (C: νSetData p): DepsRestr p 0 :=
  toDepsRestr C.(restrFrames).

Definition dgnDepsReflBelow {p} (C: νSetData p)
  (reflFramesBelow: mkReflFrameBelowTypes (dgnDepsRestr C)): DepsReflBelow p 0 :=
  {|
    _depsRestr := dgnDepsRestr C;
    _reflFramesBelow := reflFramesBelow;
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

Definition dgnDepsReflCohsInf {p} (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (reflFramesBelow: mkReflFrameBelowTypes (dgnDepsRestr C))
  (reflFramesAbove: mkReflFrameAboveTypes (dgnDepsRestr C))
  (reflPaintingsBelow: mkReflPaintingBelowTypes
    (dgnDepsReflBelow C reflFramesBelow)
    (TopRestrDep (deps := dgnDepsRestr C) E))
  (idRestrReflFramesBelow:
    mkIdRestrReflFrameBelowTypes (dgnDepsReflBelow C reflFramesBelow))
  (idRestrReflPaintingsBelow:
    mkIdRestrReflPaintingBelowTypes (dgnDepsCohs C E)
      reflFramesBelow reflPaintingsBelow idRestrReflFramesBelow)
  (cohReflRestrFramesBelowInf:
    mkCohReflRestrFrameBelowInfTypes
      (dgnDepsCohs C E) reflFramesBelow reflPaintingsBelow):
  DepsReflCohsInf p 0 :=
  {|
    _depsCohs2 := dgnDepsCohs2 C E E';
    _reflFramesBelow' := reflFramesBelow;
    _reflFramesAbove := reflFramesAbove;
    _reflPaintingsBelow := reflPaintingsBelow;
    _idRestrReflFramesBelow := idRestrReflFramesBelow;
    _idRestrReflPaintingsBelow := idRestrReflPaintingsBelow;
    _cohReflRestrFramesBelowInf := cohReflRestrFramesBelowInf;
  |}.

Definition dgnDepsReflCohsSup {p} (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (reflFramesBelow: mkReflFrameBelowTypes (dgnDepsRestr C))
  (reflFramesAbove: mkReflFrameAboveTypes (dgnDepsRestr C))
  (reflPaintingsBelow: mkReflPaintingBelowTypes
    (dgnDepsReflBelow C reflFramesBelow)
    (TopRestrDep (deps := dgnDepsRestr C) E))
  (idRestrReflFramesBelow:
    mkIdRestrReflFrameBelowTypes (dgnDepsReflBelow C reflFramesBelow))
  (idRestrReflPaintingsBelow:
    mkIdRestrReflPaintingBelowTypes (dgnDepsCohs C E)
      reflFramesBelow reflPaintingsBelow idRestrReflFramesBelow)
  (cohReflRestrFramesBelowInf:
    mkCohReflRestrFrameBelowInfTypes
      (dgnDepsCohs C E) reflFramesBelow reflPaintingsBelow)
  (cohReflRestrFramesBelowSup:
    mkCohReflRestrFrameBelowSupTypes
      (dgnDepsReflCohsInf C E E'
        reflFramesBelow reflFramesAbove reflPaintingsBelow
        idRestrReflFramesBelow idRestrReflPaintingsBelow
        cohReflRestrFramesBelowInf))
  (reflPaintingsAbove:
    mkReflPaintingAboveTypes
      (AboveOfReflCohsInf
        (dgnDepsReflCohsInf C E E'
          reflFramesBelow reflFramesAbove reflPaintingsBelow
          idRestrReflFramesBelow idRestrReflPaintingsBelow
          cohReflRestrFramesBelowInf)))
  (cohReflRestrFramesAboveSup:
    mkCohReflRestrFrameAboveSupTypes
      (dgnDepsReflCohsInf C E E'
        reflFramesBelow reflFramesAbove reflPaintingsBelow
        idRestrReflFramesBelow idRestrReflPaintingsBelow
        cohReflRestrFramesBelowInf)
      reflPaintingsAbove):
  DepsReflCohsSup p 0 :=
  {|
    _depsReflCohsInf := dgnDepsReflCohsInf C E E'
      reflFramesBelow reflFramesAbove reflPaintingsBelow
      idRestrReflFramesBelow idRestrReflPaintingsBelow
      cohReflRestrFramesBelowInf;
    _cohReflRestrFramesBelowSup := cohReflRestrFramesBelowSup;
    _reflPaintingsAbove := reflPaintingsAbove;
    _cohReflRestrFramesAboveSup := cohReflRestrFramesAboveSup;
  |}.

Definition dgnHasRefl {p} (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (reflFramesBelow: mkReflFrameBelowTypes (dgnDepsRestr C))
  (reflFramesAbove: mkReflFrameAboveTypes (dgnDepsRestr C))
  (reflPaintingsBelow: mkReflPaintingBelowTypes
    (dgnDepsReflBelow C reflFramesBelow)
    (TopRestrDep (deps := dgnDepsRestr C) E))
  (idRestrReflFramesBelow:
    mkIdRestrReflFrameBelowTypes (dgnDepsReflBelow C reflFramesBelow))
  (idRestrReflPaintingsBelow:
    mkIdRestrReflPaintingBelowTypes (dgnDepsCohs C E)
      reflFramesBelow reflPaintingsBelow idRestrReflFramesBelow)
  (cohReflRestrFramesBelowInf:
    mkCohReflRestrFrameBelowInfTypes
      (dgnDepsCohs C E) reflFramesBelow reflPaintingsBelow)
  (cohReflRestrFramesBelowSup:
    mkCohReflRestrFrameBelowSupTypes
      (dgnDepsReflCohsInf C E E'
        reflFramesBelow reflFramesAbove reflPaintingsBelow
        idRestrReflFramesBelow idRestrReflPaintingsBelow
        cohReflRestrFramesBelowInf))
  (reflPaintingsAbove:
    mkReflPaintingAboveTypes
      (AboveOfReflCohsInf
        (dgnDepsReflCohsInf C E E'
          reflFramesBelow reflFramesAbove reflPaintingsBelow
          idRestrReflFramesBelow idRestrReflPaintingsBelow
          cohReflRestrFramesBelowInf)))
  (cohReflRestrFramesAboveSup:
    mkCohReflRestrFrameAboveSupTypes
      (dgnDepsReflCohsInf C E E'
        reflFramesBelow reflFramesAbove reflPaintingsBelow
        idRestrReflFramesBelow idRestrReflPaintingsBelow
        cohReflRestrFramesBelowInf)
      reflPaintingsAbove): Type :=
  HasRefl
    (dgnDepsReflCohsSup C E E'
      reflFramesBelow reflFramesAbove reflPaintingsBelow
      idRestrReflFramesBelow idRestrReflPaintingsBelow
      cohReflRestrFramesBelowInf
      cohReflRestrFramesBelowSup
      reflPaintingsAbove
      cohReflRestrFramesAboveSup)
    E'.

Class DgnDataCore {p} (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet) := {
  reflFramesBelow: mkReflFrameBelowTypes (dgnDepsRestr C);
  reflFramesAbove: mkReflFrameAboveTypes (dgnDepsRestr C);
  reflPaintingsBelow:
    mkReflPaintingBelowTypes
      (dgnDepsReflBelow C reflFramesBelow)
      (TopRestrDep (deps := dgnDepsRestr C) E);
  idRestrReflFramesBelow:
    mkIdRestrReflFrameBelowTypes (dgnDepsReflBelow C reflFramesBelow);
  idRestrReflPaintingsBelow:
    mkIdRestrReflPaintingBelowTypes
      (dgnDepsCohs C E)
      reflFramesBelow reflPaintingsBelow idRestrReflFramesBelow;
  cohReflRestrFramesBelowInf
    (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet):
    mkCohReflRestrFrameBelowInfTypes
      (dgnDepsCohs C E) reflFramesBelow reflPaintingsBelow;
  cohReflRestrFramesBelowSup
    (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet):
    mkCohReflRestrFrameBelowSupTypes
      (dgnDepsReflCohsInf C E E'
        reflFramesBelow reflFramesAbove reflPaintingsBelow
        idRestrReflFramesBelow idRestrReflPaintingsBelow
        (cohReflRestrFramesBelowInf E'));
  reflPaintingsAbove
    (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet):
    mkReflPaintingAboveTypes
      (AboveOfReflCohsInf
        (dgnDepsReflCohsInf C E E'
          reflFramesBelow reflFramesAbove reflPaintingsBelow
          idRestrReflFramesBelow idRestrReflPaintingsBelow
          (cohReflRestrFramesBelowInf E')));
  cohReflRestrFramesAboveSup
    (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet):
    mkCohReflRestrFrameAboveSupTypes
      (dgnDepsReflCohsInf C E E'
        reflFramesBelow reflFramesAbove reflPaintingsBelow
        idRestrReflFramesBelow idRestrReflPaintingsBelow
        (cohReflRestrFramesBelowInf E'))
      (reflPaintingsAbove E');
  cohReflBelowBelowFrames
    (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet):
    mkCohReflBelowBelowFrameTypes
      (dgnDepsReflCohsInf C E E'
        reflFramesBelow reflFramesAbove reflPaintingsBelow
        idRestrReflFramesBelow idRestrReflPaintingsBelow
        (cohReflRestrFramesBelowInf E'));
  cohReflAboveBelowFrames
    (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet):
    mkCohReflAboveBelowFrameTypes
      (dgnDepsReflCohsSup C E E'
        reflFramesBelow reflFramesAbove reflPaintingsBelow
        idRestrReflFramesBelow idRestrReflPaintingsBelow
        (cohReflRestrFramesBelowInf E')
        (cohReflRestrFramesBelowSup E')
        (reflPaintingsAbove E')
        (cohReflRestrFramesAboveSup E'));
  cohReflAboveAboveFrames
    (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet):
    mkCohReflAboveAboveFrameTypes
      (dgnDepsReflCohsSup C E E'
        reflFramesBelow reflFramesAbove reflPaintingsBelow
        idRestrReflFramesBelow idRestrReflPaintingsBelow
        (cohReflRestrFramesBelowInf E')
        (cohReflRestrFramesBelowSup E')
        (reflPaintingsAbove E')
        (cohReflRestrFramesAboveSup E'));
}.

Definition dgnDepsReflCohsInfFromBase {p}
  (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (D: DgnDataCore C E): DepsReflCohsInf p 0 :=
  dgnDepsReflCohsInf C E E'
    D.(reflFramesBelow) D.(reflFramesAbove)
    D.(reflPaintingsBelow)
    D.(idRestrReflFramesBelow) D.(idRestrReflPaintingsBelow)
    (D.(cohReflRestrFramesBelowInf) E').

Definition dgnDepsReflCohsSupFromBase {p}
  (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (D: DgnDataCore C E): DepsReflCohsSup p 0 :=
  {|
    _depsReflCohsInf := dgnDepsReflCohsInfFromBase C E E' D;
    _cohReflRestrFramesBelowSup := D.(cohReflRestrFramesBelowSup) E';
    _reflPaintingsAbove := D.(reflPaintingsAbove) E';
    _cohReflRestrFramesAboveSup := D.(cohReflRestrFramesAboveSup) E';
  |}.

Definition dgnHasReflFromBase {p}
  (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (D: DgnDataCore C E): Type :=
  dgnHasRefl C E E'
    D.(reflFramesBelow) D.(reflFramesAbove)
    D.(reflPaintingsBelow)
    D.(idRestrReflFramesBelow) D.(idRestrReflPaintingsBelow)
    (D.(cohReflRestrFramesBelowInf) E')
    (D.(cohReflRestrFramesBelowSup) E')
    (D.(reflPaintingsAbove) E')
    (D.(cohReflRestrFramesAboveSup) E').

Definition dgnExtraDepsReflCohsSupFromBase {p}
  (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (D: DgnDataCore C E)
  (L: dgnHasReflFromBase C E E' D):
  DepsReflCohsSupExtension p 0 (dgnDepsReflCohsSupFromBase C E E' D) :=
  TopReflCohSupDep (deps := dgnDepsReflCohsSupFromBase C E E' D) L.

Definition dgnCohLFromBase {p}
  (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (D: DgnDataCore C E)
  (L: dgnHasReflFromBase C E E' D): Type :=
  mkCohReflAboveAbovePaintingTypes
    (dgnDepsReflCohsSupFromBase C E E' D)
    (dgnExtraDepsReflCohsSupFromBase C E E' D L)
    (D.(cohReflAboveAboveFrames) E').

Class DgnData {p} (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet) := {
  dgnDataCore: DgnDataCore C E;
  cohReflRestrPaintingsBelowInf
    (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
    (L: dgnHasReflFromBase C E E' dgnDataCore)
    (cohL: dgnCohLFromBase C E E' dgnDataCore L):
    mkCohReflRestrPaintingBelowInfTypes
      (dgnDepsReflCohsSupFromBase C E E' dgnDataCore)
      (dgnExtraDepsReflCohsSupFromBase C E E' dgnDataCore L);
  cohReflRestrPaintingsBelowSup
    (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
    (L: dgnHasReflFromBase C E E' dgnDataCore)
    (cohL: dgnCohLFromBase C E E' dgnDataCore L):
    mkCohReflRestrPaintingBelowSupTypes
      (dgnDepsReflCohsSupFromBase C E E' dgnDataCore)
      (dgnExtraDepsReflCohsSupFromBase C E E' dgnDataCore L);
  cohReflRestrPaintingsAboveSup
    (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
    (L: dgnHasReflFromBase C E E' dgnDataCore)
    (cohL: dgnCohLFromBase C E E' dgnDataCore L):
    mkCohReflRestrPaintingAboveSupTypes
      (dgnDepsReflCohsSupFromBase C E E' dgnDataCore)
      (dgnExtraDepsReflCohsSupFromBase C E E' dgnDataCore L);
  cohReflBelowBelowPaintings
    (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
    (L: dgnHasReflFromBase C E E' dgnDataCore)
    (cohL: dgnCohLFromBase C E E' dgnDataCore L):
    mkCohReflBelowBelowPaintingTypes
      (dgnDepsReflCohsSupFromBase C E E' dgnDataCore)
      (dgnExtraDepsReflCohsSupFromBase C E E' dgnDataCore L)
      (dgnDataCore.(cohReflBelowBelowFrames) E');
  cohReflAboveBelowPaintings
    (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
    (L: dgnHasReflFromBase C E E' dgnDataCore)
    (cohL: dgnCohLFromBase C E E' dgnDataCore L):
    mkCohReflAboveBelowPaintingTypes
      (dgnDepsReflCohsSupFromBase C E E' dgnDataCore)
      (dgnExtraDepsReflCohsSupFromBase C E E' dgnDataCore L)
      (dgnDataCore.(cohReflAboveBelowFrames) E');
  cohReflAboveAbovePaintings
    (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
    (L: dgnHasReflFromBase C E E' dgnDataCore)
    (cohL: dgnCohLFromBase C E E' dgnDataCore L):
    mkCohReflAboveAbovePaintingTypes
      (dgnDepsReflCohsSupFromBase C E E' dgnDataCore)
      (dgnExtraDepsReflCohsSupFromBase C E E' dgnDataCore L)
      (dgnDataCore.(cohReflAboveAboveFrames) E');
}.

Definition dgnDepsReflCohsInfFromData {p}
  (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (D: DgnData C E): DepsReflCohsInf p 0 :=
  dgnDepsReflCohsInfFromBase C E E' D.(dgnDataCore).

Definition dgnHasReflFromData {p}
  (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (D: DgnData C E): Type :=
  dgnHasReflFromBase C E E' D.(dgnDataCore).

Definition dgnDepsReflCohsSupFromData {p}
  (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (D: DgnData C E):
  DepsReflCohsSup p 0 :=
  dgnDepsReflCohsSupFromBase C E E' D.(dgnDataCore).

Definition dgnCohLFromData {p}
  (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (D: DgnData C E)
  (L: dgnHasReflFromData C E E' D): Type :=
  dgnCohLFromBase C E E' D.(dgnDataCore) L.

Definition dgnExtraDepsReflCohsSupFromData {p}
  (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (D: DgnData C E)
  (L: dgnHasReflFromData C E E' D):
  DepsReflCohsSupExtension p 0 (dgnDepsReflCohsSupFromData C E E' D) :=
  dgnExtraDepsReflCohsSupFromBase C E E' D.(dgnDataCore) L.

Definition dgnDepsReflCohs2FromData {p}
  (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (E'': mkFrame (dgnDepsRestr (mkνSetData p.+1 (mkνSetData p C E) E')) -> HSet)
  (D: DgnData C E)
  (L: dgnHasReflFromData C E E' D)
  (cohL: dgnCohLFromData C E E' D L):
  DepsReflCohs2 p 0 :=
{|
  _depsReflCohsSup := dgnDepsReflCohsSupFromData C E E' D;
  _extraDepsCohs2 := TopCoh2Dep (depsCohs2 := dgnDepsCohs2 C E E') E'';
  _extraDepsReflCohsSup := TopReflCohSupDep
    (deps := dgnDepsReflCohsSupFromData C E E' D) L;
  _cohReflRestrPaintingsBelowInf :=
    D.(cohReflRestrPaintingsBelowInf) E' L cohL;
  _cohReflRestrPaintingsBelowSup :=
    D.(cohReflRestrPaintingsBelowSup) E' L cohL;
  _cohReflRestrPaintingsAboveSup :=
    D.(cohReflRestrPaintingsAboveSup) E' L cohL;
  _cohReflBelowBelowFrames := D.(dgnDataCore).(cohReflBelowBelowFrames) E';
  _cohReflBelowBelowPaintings :=
    D.(cohReflBelowBelowPaintings) E' L cohL;
  _cohReflAboveBelowFrames := D.(dgnDataCore).(cohReflAboveBelowFrames) E';
  _cohReflAboveBelowPaintings :=
    D.(cohReflAboveBelowPaintings) E' L cohL;
  _cohReflAboveAboveFrames := D.(dgnDataCore).(cohReflAboveAboveFrames) E';
  _cohReflAboveAbovePaintings :=
    D.(cohReflAboveAbovePaintings) E' L cohL;
|}.

#[local]
Instance mkDgnData {p} (C: νSetData p)
  (E: mkFrame (dgnDepsRestr C) -> HSet)
  (E': mkFrame (dgnDepsRestr (mkνSetData p C E)) -> HSet)
  (D: DgnData C E)
  (L: dgnHasReflFromData C E E' D)
  (cohL: dgnCohLFromData C E E' D L):
  DgnData (mkνSetData p C E) E' :=
  let depsInf := dgnDepsReflCohsInfFromData C E E' D in
  let depsSup := dgnDepsReflCohsSupFromData C E E' D in
  let deps2 E'' := dgnDepsReflCohs2FromData C E E' E'' D L cohL in
  let extraSup := dgnExtraDepsReflCohsSupFromData C E E' D L in
  let base := @Build_DgnDataCore p.+1 (mkνSetData p C E) E'
    (mkReflFramesBelow depsInf)
    (mkReflFramesAbove depsSup)
    (mkReflPaintingsBelow depsSup extraSup)
    (mkIdRestrReflFramesBelow depsInf)
    (mkIdRestrReflPaintingsBelow depsSup extraSup)
    (fun E'' => mkCohReflRestrFramesBelowInf (deps2 E''))
    (fun E'' => mkCohReflRestrFramesBelowSup (deps2 E''))
    (fun _ => mkReflPaintingsAbove depsSup extraSup)
    (fun E'' => mkCohReflRestrFramesAboveSup (deps2 E''))
    (fun E'' => mkCohReflBelowBelowFrames (deps2 E''))
    (fun E'' => mkCohReflAboveBelowFrames (deps2 E''))
    (fun E'' => mkCohReflAboveAboveFrames (deps2 E'')) in
  @Build_DgnData p.+1 (mkνSetData p C E) E'
    base
    (fun E'' L' cohL' => mkCohReflRestrPaintingsBelowInf (deps2 E'')
      (TopReflCoh2Dep (deps := deps2 E'') L' cohL'.2))
    (fun E'' L' cohL' => mkCohReflRestrPaintingsBelowSup (deps2 E'')
      (TopReflCoh2Dep (deps := deps2 E'') L' cohL'.2))
    (fun E'' L' cohL' => mkCohReflRestrPaintingsAboveSup (deps2 E'')
      (TopReflCoh2Dep (deps := deps2 E'') L' cohL'.2))
    (fun E'' L' cohL' => mkCohReflBelowBelowPaintings (deps2 E'')
      (TopReflCoh2Dep (deps := deps2 E'') L' cohL'.2))
    (fun E'' L' cohL' => mkCohReflAboveBelowPaintings (deps2 E'')
      (TopReflCoh2Dep (deps := deps2 E'') L' cohL'.2))
    (fun E'' L' cohL' => mkCohReflAboveAbovePaintings (deps2 E'')
      (TopReflCoh2Dep (deps := deps2 E'') L' cohL'.2)).

Class νDgnSet p (C: νSet p) := {
  dgnPrefix: (mkνSet C).(prefix) -> Type;
  dgnData (X: (mkνSet C).(prefix)): dgnPrefix X -> DgnData (C.(data) X.1) X.2;
}.

Definition mkDgnPrefix p {C: νSet p} {D: νDgnSet p C}
  (X: (mkνSet (mkνSet C)).(prefix)): Type :=
  { R: D.(dgnPrefix) X.1 &T
    { dgnL: dgnHasReflFromData
        (C.(data) X.1.1) X.1.2 X.2 (D.(dgnData) X.1 R) &T
      dgnCohLFromData
        (C.(data) X.1.1) X.1.2 X.2 (D.(dgnData) X.1 R) dgnL } }.

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
  let base := @Build_DgnDataCore 0 mkνSetData0 E
    (tt: mkReflFrameBelowTypes (dgnDepsRestr mkνSetData0))
    (tt: mkReflFrameAboveTypes (dgnDepsRestr mkνSetData0))
    tt
    tt
    tt
    (fun _ => tt)
    (fun _ => tt)
    (fun _ => tt)
    (fun _ => tt)
    (fun _ => tt)
    (fun _ => tt)
    (fun _ => tt) in
  @Build_DgnData 0 mkνSetData0 E
    base
    (fun _ _ _ => tt)
    (fun _ _ _ => tt)
    (fun _ _ _ => tt)
    (fun _ _ _ => tt)
    (fun _ _ _ => tt)
    (fun _ _ _ => tt).

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
      mkDgnData (C.(data) X.1.1) X.1.2 X.2 (D.(dgnData) X.1 L.1) L.2.1 L.2.2;
  |}.

Fixpoint νDgnSetAt n: νDgnSet n (νSetAt n) :=
  match n with
  | O => mkνDgnSet0
  | n.+1 => mkνDgnSetSn (νSetAt n) (νDgnSetAt n)
  end.

CoInductive νDgnSetFrom n
  (X: (νSetAt n).(prefix))
  (M: νSetFrom n X)
  (R: (νDgnSetAt n).(dgnPrefix) (X; this n X M)): Type := dcons {
  dgnL: dgnHasReflFromData
    ((νSetAt n).(data) X)
    (this n X M)
    (this n.+1 (X; this n X M) (next n X M))
    ((νDgnSetAt n).(dgnData) (X; this n X M) R);
  dgnCohL: dgnCohLFromData
    ((νSetAt n).(data) X)
    (this n X M)
    (this n.+1 (X; this n X M) (next n X M))
    ((νDgnSetAt n).(dgnData) (X; this n X M) R) dgnL;
  dgnNext: νDgnSetFrom n.+1 (X; this n X M) (next n X M) (R; (dgnL; dgnCohL));
}.

Definition νDgnSets (X: νSets) := νDgnSetFrom 0 tt X tt.

End νDgnSet.

Module νDgnSetUnit := νDgnSet νSet.ArityUnit.
Module νDgnSetBool := νDgnSet νSet.ArityBool.

Definition Simplicial := νDgnSetUnit.νDgnSets.
Definition Cubical := νDgnSetBool.νDgnSets.

Example Simplicial1 :=
  Eval lazy -[leR] in (νDgnSetUnit.νDgnSetAt 1).(νDgnSetUnit.dgnPrefix).

Example Cubical1 :=
  Eval lazy -[leR] in (νDgnSetBool.νDgnSetAt 1).(νDgnSetBool.dgnPrefix).

Print Cubical1.
