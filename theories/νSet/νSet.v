From Stdlib Require Import List Logic.FunctionalExtensionality.
Import Logic.EqNotations ListNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT Notation RewLemmas HSet LeYoneda.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Set Typeclasses Depth 10.
Remove Printing Let sigT.
Remove Printing Let prod.

Section νSet.
Variable arity: HSet.

(** The type of lists [frame(p+n,0);...;frame(p+n,p-1)] for arbitrary n *)

Fixpoint FrameGen p: Type :=
  match p with
  | 0 => unit
  | S p => { frames'': FrameGen p &T HSet }
  end.

(** The type of lists [painting(p+n,0);...;painting(p+n,p-1)] for arbitrary n *)

Fixpoint PaintingGen p: FrameGen p -> Type :=
  match p with
  | 0 => fun _ => unit
  | S p => fun frames'' =>
    { painting'': PaintingGen p frames''.1 &T frames''.2 -> HSet }
  end.

Class RestrFrameTypeBlock p := {
  RestrFrameTypesDef: Type;
  FrameDef: RestrFrameTypesDef -> FrameGen p.+1;
}.

(**
For p and n be given, and assuming [frame(p-1+n,0);...;frame(p-1+n,p-1)] and
[painting(p-1+n,0);...;painting(p-1+n,p-1)], we build the list of pairs:
- of the types RestrFrameTypes(p+n,p) of the list
  [restrFrame(p+n,0);...;restrFrame(p+n,p-1)]
  (represented as an inhabitant of a sigma-type
   {R:RestrFrameTypes(p+n,0) & ... & RestrFrameTypes(p+n,p-1)})
- and of the list [frame(p+n,0);...;frame(p+n,p)] in function of effective
  restrFrames of type RestrFrameTypes(p+n,p)

That is, we build:
  p = 0 : { RestrFrameTypes := unit ;
                  (which denotes the empty list of restrFrameTypes)
                Frames(n,0..0)(restrFrames^n_{0..0-1}) := [unit]
                  (representing lists by Sigma-types) }
  p = 1 : { RestrFrameTypes = {_:unit & restrFrameType(1+n,0)} ;
                  (thus denoting the singleton list [restrFrameType(1+n,0])
                Frames(1+n,0..1)(restrFrames(1+n,0..0) :=
                  [unit;{d:Frame(1+n,0)&Painting(1+n,0)(restrFrame(1+n,0)(d)}] }
  ...
  p     : { RestrFrameTypes = {RestrFrameType(p+n,0) ...
            RestrFrameType(p+n,p-1)} ;
              Frame(p+n,p)(restrFrames(p+n,0..p-1) := [frame(p+n,0);...;
                                                       frame(p+n,p)] }
*)

Definition mkRestrFrameTypesStep {p n}
  {frames'': FrameGen p.+1}
  (paintings'': PaintingGen p.+1 frames'')
  (prev: RestrFrameTypeBlock p) :=
  { R: prev.(RestrFrameTypesDef) &T
    forall q (Hq: q <= n) (ε: arity), (prev.(FrameDef) R).2 -> frames''.2 }.

Definition mkLayer {p n}
  {frames'': FrameGen p.+1}
  {paintings'': PaintingGen p.+1 frames''}
  {prev: RestrFrameTypeBlock p}
  (restrFrames: mkRestrFrameTypesStep (n := n) paintings'' prev)
  (d: (prev.(FrameDef) restrFrames.1).2) :=
  hforall ε, paintings''.2 (restrFrames.2 0 leY_O ε d).

Fixpoint mkRestrFrameTypesAndFrames' {p n}: forall (frames'': FrameGen p)
  (paintings'': PaintingGen p frames''), RestrFrameTypeBlock p :=
  match p with
  | 0 => fun frames'' paintings'' =>
    {|
      RestrFrameTypesDef := unit;
      FrameDef _ := (tt; hunit) : FrameGen 1
    |}
  | p.+1 => fun frames'' paintings'' =>
    let prev :=
      mkRestrFrameTypesAndFrames' (n := n.+1) frames''.1 paintings''.1 in
    let frames' := prev.(FrameDef) in
    {|
      RestrFrameTypesDef := mkRestrFrameTypesStep (n := n) paintings'' prev;
      FrameDef R :=
        (frames' R.1; { d: (frames' R.1).2 & mkLayer R d }): FrameGen p.+2
    |}
  end.

Class FormDeps p n := {
  _frames'': FrameGen p;
  _paintings'': PaintingGen p _frames'';
  _restrFrames': (mkRestrFrameTypesAndFrames' _frames'' _paintings''
    (n := n)).(RestrFrameTypesDef);
}.

Generalizable Variables p n.

Definition mkFrames' `(deps: FormDeps p n): FrameGen p.+1 :=
  (mkRestrFrameTypesAndFrames' deps.(_frames'')
    deps.(_paintings'')).(FrameDef) deps.(_restrFrames').

Definition mkFrame' `(deps: FormDeps p n): HSet := (mkFrames' deps).2.

Class FormDep `(deps: FormDeps p n.+1) := {
  _frame'': HSet;
  _painting'': _frame'' -> HSet;
  _restrFrame': forall q {Hq: q <= n} (ε: arity),
    mkFrame' (n := n.+1) deps -> _frame'';
}.

#[local]
Instance consDep `(deps: FormDeps p n.+1)
  (dep: FormDep deps): FormDeps p.+1 n :=
{|
  _frames'' := (deps.(_frames''); dep.(_frame'')): FrameGen p.+1;
  _paintings'' := (deps.(_paintings''); dep.(_painting''));
  _restrFrames' := (deps.(_restrFrames'); dep.(_restrFrame'));
|}.

#[local]
Instance proj1Deps `(deps: FormDeps p.+1 n): FormDeps p n.+1 :=
{|
  _frames'' := deps.(_frames'').1;
  _paintings'' := deps.(_paintings'').1;
  _restrFrames' := deps.(_restrFrames').1;
|}.

#[local]
Instance proj2Deps `(deps: FormDeps p.+1 n): FormDep (proj1Deps deps) :=
{|
  _frame'' := deps.(_frames'').2;
  _painting'' := deps.(_paintings'').2;
  _restrFrame' := deps.(_restrFrames').2;
|}.

Declare Scope deps_scope.
Delimit Scope deps_scope with deps.
Bind Scope deps_scope with FormDeps.
Notation "x .(1)" := (proj1Deps x%_deps)
  (at level 1, left associativity, format "x .(1)"): type_scope.
Notation "x .(2)" := (proj2Deps x%_deps)
  (at level 1, left associativity, format "x .(2)"): type_scope.
Notation "( x ; y )" := (consDep x y)
  (at level 0, format "( x ; y )"): deps_scope.

Inductive FormDepsExtension {p} : forall {n}, FormDeps p n -> Type :=
| TopDep {deps}:
  forall E': mkFrame' deps -> HSet, FormDepsExtension (n := 0) deps
| AddDep {n} deps dep:
  FormDepsExtension (consDep deps dep) -> FormDepsExtension (n := n.+1) deps.

Declare Scope extra_deps_scope.
Delimit Scope extra_deps_scope with extradeps.
Bind Scope extra_deps_scope with FormDepsExtension.
Notation "( x ; y )" := (AddDep _ x y)
  (at level 0, format "( x ; y )"): extra_deps_scope.

(* Example: if p := 0, extraDeps := ([],E') mkPainting:= [E'] *)

Fixpoint mkPainting' `{deps: FormDeps p n} (extraDeps: FormDepsExtension deps):
  mkFrame' deps -> HSet :=
  match extraDeps with
  | @TopDep _ deps E' => fun (d: mkFrame' deps) => E' d
  | AddDep deps dep extraDeps => fun (d: mkFrame' deps) =>
      {l: mkLayer (deps; dep).(_restrFrames') d & mkPainting' extraDeps (d; l)}
  end.

Fixpoint mkPaintings' {p n}: forall `{deps: FormDeps p n}
  (extraDeps: FormDepsExtension deps), PaintingGen p.+1 (mkFrames' deps) :=
  match p with
  | 0 => fun deps extraDeps => (tt; mkPainting' extraDeps)
  | S p => fun deps extraDeps =>
    (mkPaintings' (deps.(2); extraDeps)%extradeps; mkPainting' extraDeps)
  end.

Lemma unfoldPaintingProj `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps} {d: mkFrame' deps}:
   mkPainting' extraDeps d = (mkPaintings' extraDeps).2 d.
Proof.
  now destruct p.
Defined.

(** Assuming [frame(p-1+n,0);...;frame(p-1+n,p-1)] and
       [painting(p-1+n,0);...;painting(p-1+n,p-1)] and
       [restrFrame(p+n,0);...;restrFrame(p+n,p-1)] (forming a "deps"),
     and assuming [frame(p-1+n,p);...;frame(p-1+n,p-1+n] and
       [painting(p-1+n,p);...;painting(p-1+n,p-1+n)] and
       [restrFrame(p+n,p);...;restrFrame(p+n,p-1+n)] as well as
       some E':frame(p+n,p+n) -> HSet (altogether forming an "extraDeps"),
     we build the list of types (represented as a Sigma-type) of restrFrames
     of the following form:
       [restrFrame(p+1+n,0);...;restrFrame(p+1+n,p)]
     (represented as an inhabitant of the Sigma-type)

     Example: if p := 0, extraDeps := ([],E')
     mkRestrFrameTypes := [unit -> unit] *)

Definition mkRestrFrameTypes `{deps: FormDeps p n}
  (extraDeps: FormDepsExtension deps) :=
  (mkRestrFrameTypesAndFrames' (n := n) (mkFrames' deps)
    (mkPaintings' extraDeps)).(RestrFrameTypesDef).

(* Same, but restricted to p-1, that is, the types of:
    [restrFrame(p+1+n,0);...;restrFrame(p+1+n,p-1)] *)

Definition mkPrevRestrFrameTypes `(deps: FormDeps p n)
  (extraDeps: FormDepsExtension deps) :=
  (mkRestrFrameTypesAndFrames' (n := n.+1) (mkFrames' deps).1
    (mkPaintings' extraDeps).1).(RestrFrameTypesDef).

(** We combining mkFrames', mkPaintings' and an assumed restrFrames.
     That is, from:
       [frame(p-1+n,0);...;frame(p-1+n,p-1)]
       [painting(p-1+n,0);...;painting(p-1+n,p-1)]
       [restrFrame(p+n,0);...;restrFrame(p+n,p-1)]
     (forming a "deps"), and
       [frame(p-1+n,p);...;frame(p-1+n,p-1+n]
       [painting(p-1+n,p);...;painting(p-1+n,p-1+n)]
       [restrFrame(p+n,p);...;restrFrame(p+n,p-1+n)]
       E':frame(p+n,p+n) -> HSet
     (forming an "extraDeps"), and
       [restrFrame(p+1+n,0);...;restrFrame(p+1+n,p)],
     we form:
       [frame(p+n,0);...;frame(p+n,p)] (built by mkFrames')
       [painting(p+n,0);...;painting(p+n,p)] (built by mkPaintings')
       [restrFrame(p+n,0);...;restrFrame(p+n,p)] *)

Definition mkDeps `{deps: FormDeps p n} {extraDeps: FormDepsExtension deps}
  (restrFrames: mkRestrFrameTypes extraDeps) :=
{|
  _frames'' := mkFrames' deps;
  _paintings'' := mkPaintings' extraDeps;
  _restrFrames' := restrFrames;
|}.

(** Thus being able to build frame(p+1+n,p+1) from the same assumptions *)

Definition mkFrame `{deps: FormDeps p n} {extraDeps: FormDepsExtension deps}
  (restrFrames: mkRestrFrameTypes extraDeps) :=
  mkFrame' (mkDeps restrFrames).

(** By restriction, we can thus build frame(p+1+n,p). Note that mkPrevFrame
    could not be built by calling mkFrame' on p and n+1 (rather than on
    p+1 and n, then restricting) because it would require knowing deps for
    p and n+1 instead of only p and n *)

Definition mkPrevFrame `{deps: FormDeps p n} {extraDeps: FormDepsExtension deps}
  (restrFrames: mkRestrFrameTypes extraDeps) :=
  mkFrame' (mkDeps restrFrames).(1).

Class CohFrameTypeBlock `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps} := {
  CohFrameTypesDef: Type;
  RestrFramesDef: CohFrameTypesDef -> mkRestrFrameTypes extraDeps
}.

Definition RestrPaintingType' `{deps: FormDeps p n.+1} (dep: FormDep deps)
  (extraDeps: FormDepsExtension (deps; dep)) :=
  forall q (Hq: q <= n) ε (d: mkFrame' deps),
  (mkPaintings' (dep; extraDeps)).2 d ->
  dep.(_painting'') (dep.(_restrFrame') q ε d).

Fixpoint RestrPaintingTypes' {p}: forall `{deps: FormDeps p n}
  (extraDeps: FormDepsExtension deps), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun n deps extraDeps =>
    { R: RestrPaintingTypes' (deps.(2); extraDeps) &T
      RestrPaintingType' deps.(2) extraDeps }
  end.

Definition mkCohFrameTypesStep `{deps: FormDeps p.+1 n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  (prev: CohFrameTypeBlock (extraDeps := (deps.(2); extraDeps))): Type :=
  { Q: prev.(CohFrameTypesDef) &T
    forall r q (Hrq: r <= q) (Hq: q <= n) (ε ω: arity) d,
    deps.(_restrFrames').2 q Hq ε
      ((prev.(RestrFramesDef) Q).2 r (Hrq ↕ (↑ Hq)) ω d) =
    deps.(_restrFrames').2 r (Hrq ↕ Hq) ω
      ((prev.(RestrFramesDef) Q).2 q.+1 (⇑ Hq) ε d) }.

Definition mkRestrLayer `{deps: FormDeps p.+1 n}
  {extraDeps: FormDepsExtension deps}
  (restrPaintings': RestrPaintingTypes' extraDeps)
  {prev: CohFrameTypeBlock (extraDeps := (deps.(2); extraDeps))}
  (cohFrames: mkCohFrameTypesStep (restrPaintings' := restrPaintings') prev)
  q (Hq: q <= n) (ε: arity)
  (d: mkPrevFrame (prev.(RestrFramesDef) cohFrames.1)):
  mkLayer (prev.(RestrFramesDef) cohFrames.1) d -> mkLayer deps.(_restrFrames')
    ((prev.(RestrFramesDef) cohFrames.1).2 q.+1 (⇑ Hq) ε d) :=
  fun l ω => rew [deps.(_paintings'').2] cohFrames.2 0 q leY_O Hq ε ω d in
             restrPaintings'.2 q Hq ε _ (l ω).

(** Under previous assumptions, and, additionally:
      [restrPainting(p+n,0);...;restrPainting(p+n,p-1)]
    we mutually build the pair of:
    - the list of types for [cohFrame(p+1+n,0);...;cohFrame(p+1+n,p-1)]
    - definitions of [restrFrame(p+1+n,0);...;restrFrame(p+1+n,p)] *)

#[local]
Instance mkCohFrameTypesAndRestrFrames:
  forall `{deps: FormDeps p n} {extraDeps: FormDepsExtension deps}
  (restrPaintings': RestrPaintingTypes' extraDeps), CohFrameTypeBlock :=
  fix mkCohFrameTypesAndRestrFrames {p}:
  forall `(deps: FormDeps p n) (extraDeps: FormDepsExtension deps)
    (restrPaintings': RestrPaintingTypes' extraDeps), CohFrameTypeBlock :=
  match p with
  | 0 =>
    fun n deps extraDeps restrPaintings' =>
    {|
      CohFrameTypesDef := unit;
      RestrFramesDef _ := (tt; fun _ _ _ _ => tt)
    |}
  | S p =>
    fun n deps extraDeps restrPaintings' =>
    let prev := mkCohFrameTypesAndRestrFrames deps.(1)
      (deps.(2); extraDeps)%extradeps restrPaintings'.1 in
    let restrFrames := prev.(RestrFramesDef) in
    let cohFrameTypes := prev.(CohFrameTypesDef) in
    {|
      CohFrameTypesDef := mkCohFrameTypesStep prev;
      RestrFramesDef Q :=
      (* RestrFrame(n+2,p+1) *)
      let restrFrame q (Hq: q <= n) ε
        (d: mkFrame (extraDeps := (deps.(2); extraDeps)) (restrFrames Q.1)) :=
          ((restrFrames Q.1).2 q.+1 (⇑ Hq) ε d.1;
           mkRestrLayer restrPaintings' Q q _ ε d.1 d.2)
      in (restrFrames Q.1; restrFrame)
    |}
  end.

(* Example: if p := 0, extraDeps := ([],E')
   mkCohFrameTypes := [] *)

Definition mkCohFrameTypes `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  (restrPaintings': RestrPaintingTypes' extraDeps) :=
  (mkCohFrameTypesAndRestrFrames restrPaintings').(CohFrameTypesDef).

Class DepsCohs p n := {
  deps: FormDeps p n;
  extraDeps: FormDepsExtension deps;
  restrPaintings': RestrPaintingTypes' extraDeps;
  cohs: mkCohFrameTypes restrPaintings';
}.

#[local]
Instance mkDepsCohs0 `{deps: FormDeps p 0} {E': mkFrame' deps -> HSet}
  {restrPaintings': RestrPaintingTypes' (TopDep E')}
  (cohs: mkCohFrameTypes restrPaintings'): DepsCohs p 0 := {| cohs := cohs |}.

#[local]
Instance slideDepsCohs `(depsCohs: DepsCohs p.+1 n): DepsCohs p n.+1 :=
{|
  deps := depsCohs.(deps).(1);
  extraDeps := (depsCohs.(deps).(2); depsCohs.(extraDeps));
  restrPaintings' := depsCohs.(restrPaintings').1;
  cohs := depsCohs.(cohs).1;
|}.

Definition mkRestrFrames `{depsCohs: DepsCohs p n} :=
  (mkCohFrameTypesAndRestrFrames depsCohs.(restrPaintings')).(RestrFramesDef)
    depsCohs.(cohs).

(* Tying the loop: we type mkRestrFrame((p+1)+n,p) knowing
    mkRestrFrames(p+(1+n),0..p-1)
    Note that even if mkRestrFrames((p+1)+n,p) : mkRestrFrameTypes((p+1)+n,p),
    we don't have mkRestrFrame((p+1)+n,p): mkRestrFrameType((p+1)+n,p), because
    mkRestrFrameType((p+1)+n,p) assumes restrFrames((p+1)+n,0..p) which would be
    circular.
    Instead, we only require restrFrames(p+(1+n),0..p-1) then build the type of
    restrFrame(p+1+n,p) as: Frame(p+(1+n),p) -> Frame(p+n,p)
    At the end, with only the addition of restrPaintings' and cohs, the loop is gone *)

Definition mkRestrFrameType `{depsCohs: DepsCohs p n} :=
  forall q (Hq: q <= n) (ε: arity),
  mkPrevFrame (mkRestrFrames) -> mkFrame' depsCohs.(deps).

Definition mkRestrFrame `{depsCohs: DepsCohs p n}: mkRestrFrameType :=
  mkRestrFrames.2.

(* Example: if p := 0, extraDeps := ([],E'), restrPaintings' := , cohs := []
   then mkFullDeps := {_frames'':=[unit];
                       _paintings'':=[E']};
                       _restrFrames':=[\qω().()]}
   (where _restrFrames' is presented as a dependent pair, i.e. ((),\qω().()) *)

Definition mkFullDeps `{depsCohs: DepsCohs p n} := mkDeps mkRestrFrames.

Definition mkCohFrameType `{depsCohs: DepsCohs p.+1 n} :=
  forall r q (Hrq: r <= q) (Hq: q <= n) (ε ω: arity) d,
  depsCohs.(deps).(2).(_restrFrame') q ε (mkRestrFrame r (Hrq ↕ (↑ Hq)) ω d)
  = depsCohs.(deps).(2).(_restrFrame') r (Hq := Hrq ↕ Hq) ω
      (mkRestrFrame q.+1 (⇑ Hq) ε d).

Inductive CohFramesExtension {p}: forall `(depsCohs: DepsCohs p n), Type :=
| TopCohFrame `{depsCohs: DepsCohs p 0} (E: mkFrame mkRestrFrames -> HSet):
  CohFramesExtension depsCohs
| AddCohFrame {n} (depsCohs: DepsCohs p.+1 n):
  CohFramesExtension depsCohs -> CohFramesExtension (slideDepsCohs depsCohs).

Declare Scope extra_cohs_scope.
Delimit Scope extra_cohs_scope with extracohs.
Bind Scope extra_cohs_scope with CohFramesExtension.
Notation "( x ; y )" := (AddCohFrame x y)
  (at level 0, format "( x ; y )"): extra_cohs_scope.

Fixpoint mkExtraDeps `{depsCohs: DepsCohs p n}
  (extraCohs: CohFramesExtension depsCohs): FormDepsExtension mkFullDeps.
Proof.
  destruct extraCohs.
  - now constructor.
  - unshelve econstructor.
    + now exact mkFullDeps.(2).
    + now exact (mkExtraDeps p.+1 n depsCohs extraCohs).
Defined.

Definition mkPainting `{depsCohs: DepsCohs p n}
  (extraCohs: CohFramesExtension depsCohs):
  mkFrame mkRestrFrames -> HSet :=
  mkPainting' (mkExtraDeps extraCohs).

Definition mkPrevPainting `{depsCohs: DepsCohs p n}
  (extraCohs: CohFramesExtension depsCohs):
  mkPrevFrame mkRestrFrames -> HSet :=
  mkPainting' (mkFullDeps.(2); mkExtraDeps extraCohs)%extradeps.

(* Note: We could type mkRestrPainting(p+1+n,p) of type
   RestrPaintingType(p+1+n,p) up to using unfoldPaintingProj at other places.
   It is more convenient to refer to mkPrevPainting to later state cohPainting.
*)

Definition mkRestrPaintingType `{depsCohs: DepsCohs p n}
  (extraCohs: CohFramesExtension depsCohs) :=
  forall q (Hq: q <= n) ε (d: mkPrevFrame mkRestrFrames),
  mkPrevPainting extraCohs d ->
  (mkPaintings' depsCohs.(extraDeps)).2 (mkRestrFrame q Hq ε d).

(* Note: a priori, unfoldPaintingProj can be avoided because only
   "mkRestrPaintingType 0" and "mkRestrPaintingType p.+1" are later used,
   so unfoldPaintingProj would then reduce in each cases *)

Fixpoint mkRestrPainting `{depsCohs: DepsCohs p n}
  (extraCohs: CohFramesExtension depsCohs): mkRestrPaintingType extraCohs.
Proof.
  red; intros * (l, c). destruct extraCohs, q; try now exact (l ε).
  - exfalso; now apply leY_O_contra in Hq.
  - rewrite <- unfoldPaintingProj. unshelve esplit.
    + now exact (mkRestrLayer depsCohs.(restrPaintings') depsCohs.(cohs)
      q (⇓ Hq) ε d l).
    + now exact (mkRestrPainting p.+1 n depsCohs extraCohs q (⇓ Hq) ε (d; l) c).
Defined.

Definition mkRestrPaintingTypes `{depsCohs: DepsCohs p n}
  (extraCohs: CohFramesExtension depsCohs) :=
  RestrPaintingTypes' (mkExtraDeps extraCohs).

Fixpoint mkRestrPaintings `{depsCohs: DepsCohs p n}
  (extraCohs: CohFramesExtension depsCohs): mkRestrPaintingTypes extraCohs.
Proof.
  destruct p.
  - unshelve esplit. now exact tt.
    now exact (mkRestrPainting extraCohs).
  - unshelve esplit.
    now exact (mkRestrPaintings p n.+1 (slideDepsCohs depsCohs)
      (depsCohs; extraCohs)%extracohs).
    now exact (mkRestrPainting extraCohs).
Defined.

Definition mkCohPaintingType `{depsCohs: DepsCohs p.+1 n}
  (extraCohs: CohFramesExtension depsCohs) :=
  forall r q (Hrq: r <= q) (Hq: q <= n) (ε ω: arity)
    (d: mkPrevFrame mkRestrFrames)
    (c: (mkPaintings' (mkFullDeps.(2); mkExtraDeps (depsCohs; extraCohs))).2 d),
  rew [depsCohs.(deps).(2).(_painting'')] depsCohs.(cohs).2 r q Hrq Hq ε ω d in
  depsCohs.(restrPaintings').2 q Hq ε _
    ((mkRestrPaintings (depsCohs; extraCohs)).2 r _ ω d c) =
  depsCohs.(restrPaintings').2 r (Hrq ↕ Hq) ω _
    ((mkRestrPaintings (depsCohs; extraCohs)).2 q.+1 _ ε d c).

Fixpoint mkCohPaintingTypes {p}: forall `{depsCohs: DepsCohs p n}
  (extraCohs: CohFramesExtension depsCohs), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun n depsCohs extraCohs =>
    { R: mkCohPaintingTypes (depsCohs; extraCohs) &T
         mkCohPaintingType extraCohs }
  end.

Definition mkCohLayer `{depsCohs: DepsCohs p.+1 n}
  {extraCohs: CohFramesExtension depsCohs}
  (cohPaintings: mkCohPaintingTypes extraCohs)
  {prevCohFrames: mkCohFrameTypes
    (extraDeps := (mkFullDeps.(2); mkExtraDeps extraCohs))
    (mkRestrPaintings extraCohs).1}
  r q {Hrq: r <= q} {Hq: q <= n} (ε ω: arity)
  (d: mkPrevFrame (mkRestrFrames (depsCohs := {| cohs := prevCohFrames.1 |})))
  (l: mkLayer mkRestrFrames d):
  rew [mkLayer _] prevCohFrames.2 r.+1 q.+1 (⇑ Hrq) (⇑ Hq) ε ω d in
    mkRestrLayer restrPaintings' depsCohs.(cohs) q Hq ε _
      (mkRestrLayer (mkRestrPaintings extraCohs).1 _ r (Hrq ↕ ↑ Hq) ω d l) =
    mkRestrLayer restrPaintings' depsCohs.(cohs) r (Hrq ↕ Hq) ω _
      (mkRestrLayer (mkRestrPaintings extraCohs).1 _ q.+1 (⇑ Hq) ε d l).
Proof.
  apply functional_extensionality_dep; intros 𝛉.
  rewrite <- map_subst_app. unfold mkRestrLayer; simpl.
  rewrite
    <- map_subst with (f := fun x => depsCohs.(restrPaintings').2 q Hq ε x),
    <- map_subst with
        (f := fun x => depsCohs.(restrPaintings').2 r (Hrq ↕ Hq) ω x),
    -> rew_map with (P := fun x => depsCohs.(deps).(_paintings'').2 x)
        (f := fun x => depsCohs.(deps).(_restrFrames').2 O leY_O 𝛉 x),
    -> rew_map with (P := fun x => depsCohs.(deps).(_paintings'').2 x)
        (f := fun x => depsCohs.(deps).(2).(_restrFrame') r
          (Hq := Hrq ↕ Hq) ω x),
    -> rew_map with (P := fun x => depsCohs.(deps).(_paintings'').2 x)
        (f := fun x => depsCohs.(deps).(2).(_restrFrame') q ε x),
    <- cohPaintings.2.
  repeat rewrite rew_compose.
  apply rew_swap with (P := fun x => depsCohs.(deps).(_paintings'').2 x).
  rewrite rew_app_rl. now trivial.
  now apply depsCohs.(deps).(2).(_frame'').(UIP).
Defined.

Fixpoint mkCohFrames `{depsCohs: DepsCohs p n}
  {extraCohs: CohFramesExtension depsCohs}
  (cohPaintings: mkCohPaintingTypes extraCohs) {struct p}:
  mkCohFrameTypes (mkRestrPaintings extraCohs).
Proof.
  destruct p.
  - unshelve esplit. now exact tt. now intros.
  - unshelve esplit.
    + now exact (mkCohFrames p n.+1 (slideDepsCohs depsCohs)
      (depsCohs; extraCohs)%extracohs cohPaintings.1).
    + intros r q Hrq Hq ε ω d. unshelve eapply eq_existT_curried.
      now exact ((mkCohFrames p n.+1 (slideDepsCohs depsCohs)
        (depsCohs; extraCohs)%extracohs
        cohPaintings.1).2 r.+1 q.+1 (⇑ Hrq) (⇑ Hq) ε ω d.1).
      now exact (mkCohLayer cohPaintings r q ε ω d.1 d.2).
Defined.

#[local]
Instance mkDepsCohs `{depsCohs: DepsCohs p n}
  {extraCohs: CohFramesExtension depsCohs}
  (cohPaintings: mkCohPaintingTypes extraCohs): DepsCohs p.+1 n :=
{|
  deps := mkFullDeps;
  extraDeps := mkExtraDeps extraCohs;
  restrPaintings' := mkRestrPaintings extraCohs;
  cohs := mkCohFrames cohPaintings;
|}.

Inductive CohPaintingsExtension {p}: forall `{depsCohs: DepsCohs p n}
  {extraCohs: CohFramesExtension depsCohs},
  mkCohPaintingTypes extraCohs -> Type :=
| TopCohPainting `{depsCohs: DepsCohs p 0} {E: mkFrame mkRestrFrames -> HSet}
  {cohPaintings: mkCohPaintingTypes (TopCohFrame E)}
  {NextE: mkFrame (mkRestrFrames (depsCohs := mkDepsCohs cohPaintings)) -> HSet}
  : CohPaintingsExtension cohPaintings
| AddCohPainting {n} {depsCohs: DepsCohs p.+1 n}
  {extraCohs: CohFramesExtension depsCohs}
  (cohPaintings: mkCohPaintingTypes extraCohs):
  CohPaintingsExtension cohPaintings -> CohPaintingsExtension cohPaintings.1.

Declare Scope extra_cohps_scope.
Delimit Scope extra_cohps_scope with extracohps.
Bind Scope extra_cohps_scope with CohPaintingsExtension.
Notation "( x ; y )" := (AddCohPainting x y)
  (at level 0, format "( x ; y )"): extra_cohps_scope.

Fixpoint mkExtraCohs `{depsCohs: DepsCohs p n}
  {extraCohs: CohFramesExtension depsCohs}
  {cohPaintings: mkCohPaintingTypes extraCohs}
  (extraCohPaintings: CohPaintingsExtension cohPaintings):
  CohFramesExtension (mkDepsCohs cohPaintings).
Proof.
  destruct extraCohPaintings.
  - now constructor.
  - apply (AddCohFrame (mkDepsCohs cohPaintings)).
    now exact (mkExtraCohs p.+1 n depsCohs extraCohs
      cohPaintings extraCohPaintings).
Defined.

Lemma unfoldRestrPaintings `{depsCohs: DepsCohs p n}
  {extraCohs: CohFramesExtension depsCohs} q {Hq : q <= n} ε
  (d: mkFrame' mkFullDeps.(1))
  (c: (mkPaintings' (mkFullDeps.(2); mkExtraDeps extraCohs)).2 d):
  (mkRestrPaintings extraCohs).2 q Hq ε d c =
  mkRestrPainting extraCohs q Hq ε d (rew <- unfoldPaintingProj in c).
Proof.
  now destruct p.
Defined.

Fixpoint mkCohPainting `{depsCohs: DepsCohs p n}
  {extraCohs: CohFramesExtension depsCohs}
  {cohPaintings: mkCohPaintingTypes extraCohs}
  (extraCohPaintings: CohPaintingsExtension cohPaintings):
  mkCohPaintingType (mkExtraCohs extraCohPaintings).
Proof.
  red; intros *.
  repeat rewrite unfoldRestrPaintings; rewrite rew_opp_l.
  destruct unfoldPaintingProj, c as (l, c), extraCohPaintings, r, q;
  unfold mkRestrLayer; simpl; try now rewrite unfoldRestrPaintings.
  - exfalso; now apply leY_O_contra in Hrq.
  - exfalso; now apply leY_O_contra in Hq.
  - exfalso; now apply leY_O_contra in Hrq.
  - rewrite <- rew_permute_ll_hset with
      (P := mkPainting' (depsCohs.(deps).(2); depsCohs.(extraDeps))).
    apply rew_swap.
    do 2 rewrite rew_opp_l.
    unshelve eapply (rew_existT_curried
      (Q := mkPainting' depsCohs.(extraDeps))).
    now exact (mkCohLayer cohPaintings r q (Hrq := ⇓ Hrq) ε ω d l).
    now exact (mkCohPainting p.+1 n depsCohs extraCohs
      cohPaintings extraCohPaintings r q (⇓ Hrq) (⇓ Hq) ε ω (d; l) c).
Defined.

Fixpoint mkCohPaintings `{depsCohs: DepsCohs p n}
  {extraCohs: CohFramesExtension depsCohs}
  {cohPaintings: mkCohPaintingTypes extraCohs}
  (extraCohPaintings: CohPaintingsExtension cohPaintings) {struct p}:
  mkCohPaintingTypes (mkExtraCohs extraCohPaintings).
Proof.
  destruct p.
  - unshelve esplit. now exact tt.
    now exact (mkCohPainting extraCohPaintings).
  - unshelve esplit. now exact (mkCohPaintings p n.+1
      (slideDepsCohs depsCohs) (depsCohs; extraCohs)%extracohs
      cohPaintings.1 (cohPaintings; extraCohPaintings)%extracohps).
    now exact (mkCohPainting extraCohPaintings).
Defined.

Class νSetAux p := {
  _deps: FormDeps p 0;
  _restrPaintings' E': RestrPaintingTypes' (TopDep E');
  _cohFrames E': mkCohFrameTypes (_restrPaintings' E');
  _cohPaintings E' E : mkCohPaintingTypes
    (depsCohs := mkDepsCohs0 (_cohFrames E')) (TopCohFrame E);
}.

Class νSet p := {
  prefix'': Type;
  data: prefix'' -> νSetAux p;
}.

(***************************************************)
(** The construction of [νSet n+1] from [νSet n] *)

(** Extending the initial prefix *)
Definition mkPrefix'' p {C: νSet p}: Type :=
  { D: C.(prefix'') &T mkFrame' (C.(data) D).(_deps) -> HSet }.

Section νSetData.
Variable p: nat.
Variable C: νSet p.
Variable D: mkPrefix'' p.

Definition mkDepsCohs'': DepsCohs p 0 :=
  mkDepsCohs0 ((C.(data) D.1).(_cohFrames) D.2).

Definition mkDeps': FormDeps p.+1 0 :=
  mkFullDeps (depsCohs := mkDepsCohs'').

Definition mkRestrPaintings' E': RestrPaintingTypes' (TopDep E') :=
  mkRestrPaintings (depsCohs := mkDepsCohs'') (TopCohFrame E').

Definition mkCohFrames' E': mkCohFrameTypes (mkRestrPaintings' E') :=
  mkCohFrames (depsCohs := mkDepsCohs'')
    ((C.(data) D.1).(_cohPaintings) D.2 E').

Definition mkDepsCohs' E': DepsCohs p.+1 0 :=
  mkDepsCohs0 (mkCohFrames' E').

Definition mkCohPaintings' E' E:
  mkCohPaintingTypes (depsCohs := mkDepsCohs' E') (TopCohFrame E) :=
 mkCohPaintings (TopCohPainting (NextE := E)).

End νSetData.

#[local]
Instance mkνSet0: νSet 0.
  unshelve esplit.
  - now exact hunit.
  - unshelve esplit; try now trivial. unshelve esplit; now trivial.
Defined.

#[local]
Instance mkνSet {p} (C: νSet p): νSet p.+1 :=
{|
  prefix'' := mkPrefix'' p;
  data := fun D : mkPrefix'' p =>
  {|
    _deps := mkDeps' p C D;
    _restrPaintings' := mkRestrPaintings' p C D;
    _cohFrames := mkCohFrames' p C D;
    _cohPaintings := mkCohPaintings' p C D
  |}
|}.

(** An [νSet] truncated up to dimension [n] *)
Fixpoint νSetAt n: νSet n :=
  match n with
  | O => mkνSet0
  | n.+1 => mkνSet (νSetAt n)
  end.

CoInductive νSetFrom n (X: (νSetAt n).(prefix'')): Type := cons {
  this: mkFrame' ((νSetAt n).(data) X).(_deps) -> HSet;
  next: νSetFrom n.+1 (X; this);
}.

(** The final construction *)
Definition νSets := νSetFrom 0 tt.

End νSet.

Definition AugmentedSemiSimplicial := νSets hunit.
Definition SemiSimplicial := νSetFrom hunit 1 (tt; fun _ => hunit).
Definition SemiCubical := νSets hbool.

(** Some examples *)

Example SemiSimplicial4 := Eval compute in (νSetAt hunit 4).(prefix'' _).
Print SemiSimplicial4.
