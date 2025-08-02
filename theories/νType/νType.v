Require Import List.
Import Logic.EqNotations ListNotations.
Require Import Logic.FunctionalExtensionality.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT Notation RewLemmas HSet LeYoneda.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Set Typeclasses Depth 10.
Remove Printing Let sigT.
Remove Printing Let prod.

Section νType.
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
  | S p => fun frames'' => { painting'': PaintingGen p frames''.1 &T
                             frames''.2 -> HSet }
  end.

Class RestrFrameTypeBlock p := {
  RestrFrameTypesDef: Type;
  FrameDef: RestrFrameTypesDef -> FrameGen p.+1;
}.

Inductive ExtensionGen {p frames''} {paintings'': PaintingGen p frames''}:
  forall {n: nat}, Type :=
| TopPrev: ExtensionGen (n := 0)
| AddExtraPrev {n: nat} {frame'': HSet} {painting'': frame'' -> HSet}:
   ExtensionGen (p := p.+1) (frames'' := (frames''; frame''))
     (paintings'' := (paintings''; painting'')) (n := n) ->
   ExtensionGen (frames'' := frames'') (paintings'' := paintings'') (n := n.+1).

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
  p     : { RestrFrameTypes = {RestrFrameType(p+n,0) ... RestrFrameType(p+n,p-1)} ;
              Frame(p+n,p)(restrFrames(p+n,0..p-1) := [frame(p+n,0);...;frame(p+n,p)] }
*)
Fixpoint mkRestrFrameTypesAndFrames' {p n}: forall
  frames'' (paintings'': PaintingGen p frames''), RestrFrameTypeBlock p :=
  match p with
  | 0 => fun frames'' paintings'' =>
    {|
      RestrFrameTypesDef := unit;
      FrameDef _ := (tt; hunit) : FrameGen 1
    |}
  | p.+1 => fun frames'' paintings'' =>
    let frames' := (mkRestrFrameTypesAndFrames' (n := n.+1) frames''.1 paintings''.1).(FrameDef) in
    {|
      RestrFrameTypesDef :=
        { R: (mkRestrFrameTypesAndFrames' frames''.1 paintings''.1).(RestrFrameTypesDef) &T
          forall q (Hq: q <= n) (ε: arity), (frames' R).2 -> frames''.2 };
      FrameDef R :=
        (frames' R.1; { d: (frames' R.1).2 & hforall ε, paintings''.2 (R.2 0 leY_O ε d) }) : FrameGen p.+2
    |}
  end.

Definition mkRestrFrameTypes' p n frames'' paintings'' :=
  (mkRestrFrameTypesAndFrames' frames'' paintings'' (p := p)
    (n := n)).(RestrFrameTypesDef).

Class FormDeps {p n} := {
  _frames'': FrameGen p;
  _paintings'': PaintingGen p _frames'';
  _restrFrames': mkRestrFrameTypes' p n _frames'' _paintings'';
}.

Arguments FormDeps p n: clear implicits.
Generalizable Variables p n.

Definition mkFrames' `(deps: FormDeps p n): FrameGen p.+1 :=
  (mkRestrFrameTypesAndFrames' deps.(_frames'')
    deps.(_paintings'') (n := n)).(FrameDef) deps.(_restrFrames').

Definition mkFrame' `(deps: FormDeps p n): HSet :=
  (mkFrames' deps).2.

Class FormDep `(deps: FormDeps p n.+1) := {
  _frame'': HSet;
  _painting'': _frame'' -> HSet;
  _restrFrame': forall q (Hq: q <= n) (ε: arity),
    mkFrame' (n := n.+1) deps -> _frame''.(Dom);
}.

#[local]
Instance ConsDep `(deps: FormDeps p n.+1)
  (dep: FormDep deps): FormDeps p.+1 n :=
{|
  _frames'' := (deps.(_frames''); dep.(_frame'')): FrameGen p.+1;
  _paintings'' := (deps.(_paintings''); dep.(_painting''));
  _restrFrames' := (deps.(_restrFrames'); dep.(_restrFrame'));
|}.

#[local]
Instance Proj1Deps `(deps: FormDeps p.+1 n): FormDeps p n.+1 := {|
  _frames'' := deps.(_frames'').1;
  _paintings'' := deps.(_paintings'').1;
  _restrFrames' := deps.(_restrFrames').1;
|}.

#[local]
Instance Proj2Deps `(deps: FormDeps p.+1 n): FormDep (Proj1Deps deps) := {|
  _frame'' := deps.(_frames'').2;
  _painting'' := deps.(_paintings'').2;
  _restrFrame' := deps.(_restrFrames').2;
|}.

Declare Scope deps_scope.
Delimit Scope deps_scope with deps.
Bind Scope deps_scope with FormDeps.
Notation "x .(1)" := (Proj1Deps x%_deps)
  (at level 1, left associativity, format "x .(1)"): type_scope.
Notation "x .(2)" := (Proj2Deps x%_deps)
  (at level 1, left associativity, format "x .(2)"): type_scope.
Notation "( x ; y )" := (ConsDep x y)
  (at level 0, format "( x ; y )"): deps_scope.

Inductive FormDepsExtension {p} : forall {n}, FormDeps p n -> Type :=
| TopRestrFrames {deps}:
  forall E': mkFrame' deps -> HSet,
  FormDepsExtension (n := 0) deps
| AddExtraRestrFrame {n} deps dep:
  FormDepsExtension (ConsDep deps dep) ->
  FormDepsExtension (n := n.+1) deps.

Declare Scope extra_deps_scope.
Delimit Scope extra_deps_scope with extradeps.
Bind Scope extra_deps_scope with FormDepsExtension.
Notation "( x ; y )" := (AddExtraRestrFrame _ x y)
  (at level 0, format "( x ; y )"): extra_deps_scope.

(* Example: if p := 0, extraDeps := ([],E')
   mkPainting:= [E'] *)

Fixpoint mkPainting' `{deps: FormDeps p n} (extraDeps: FormDepsExtension deps):
  mkFrame' deps -> HSet :=
  match extraDeps with
  | @TopRestrFrames _ deps E' => fun (d: mkFrame' deps) => E' d
  | AddExtraRestrFrame deps dep extraDeps => fun (d: mkFrame' deps) =>
      {l: hforall ε, dep.(_painting'') (dep.(_restrFrame') 0 leY_O ε d) &
       mkPainting' extraDeps (d; l)}
  end.

Definition MatchPainting (loop: forall `{deps: FormDeps p n}
  (extraDeps: FormDepsExtension deps),
  PaintingGen p.+1 (mkFrames' deps)) {p n} :=
  match p return forall `(deps: FormDeps p n)
  (extraDeps: FormDepsExtension deps), PaintingGen p (mkFrames' deps).1 with
  | 0 => fun _ _ => tt
  | S p => fun deps extraDeps =>
    loop (deps.(2); extraDeps)%extradeps
  end.

Fixpoint mkPaintings' `{deps: FormDeps p n}
  (extraDeps: FormDepsExtension deps):
  PaintingGen p.+1 (mkFrames' deps) :=
  (MatchPainting (@mkPaintings') deps extraDeps; mkPainting' extraDeps).

Lemma unfoldPaintingProj `{deps: FormDeps p n}
  (extraDeps: FormDepsExtension deps) restrFrame:
  (mkPaintings' extraDeps).2 restrFrame =
    mkPainting' extraDeps restrFrame.
Proof.
  destruct p; now easy.
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

Definition mkRestrFrameTypes `(deps: FormDeps p n)
  (extraDeps: FormDepsExtension deps) :=
  (mkRestrFrameTypesAndFrames' (p := p.+1) (n := n) (mkFrames' deps)
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

Definition mkDeps `{deps: FormDeps p n}
  (extraDeps: FormDepsExtension deps)
  (restrFrames: mkRestrFrameTypes deps extraDeps) :=
{|
  _frames'' := mkFrames' deps;
  _paintings'' := mkPaintings' extraDeps;
  _restrFrames' := restrFrames;
|}.

(** Thus being able to build frame(p+1+n,p+1) from
     the same assumptions *)

Definition mkFrame `{deps: FormDeps p n}
  (extraDeps: FormDepsExtension deps)
  (restrFrames: mkRestrFrameTypes deps extraDeps) :=
  mkFrame' (mkDeps extraDeps restrFrames).

(** By restriction, we can thus build frame(p+1+n,p).
    Note that mkPrevFrame could not be built by calling
    mkFrame' on p and n+1 (rather than on p+1 and n, then
    restricting) because it would require knowing deps for
    p and n+1 instead of only p and n *)

Definition mkPrevFrame `{deps: FormDeps p n}
  (extraDeps: FormDepsExtension deps)
  (restrFrames: mkRestrFrameTypes deps extraDeps) :=
  mkFrame' (mkDeps extraDeps restrFrames).(1).

Class CohFrameTypeBlock `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps} := {
  CohFrameTypesDef: Type;
  RestrFramesDef: CohFrameTypesDef ->
    mkRestrFrameTypes deps extraDeps
}.

Definition RestrPaintingType' `{deps: FormDeps p n.+1} (dep: FormDep deps)
  (extraDeps: FormDepsExtension (deps; dep)) :=
  forall q (Hq: q <= n) ε (d: mkFrame' deps),
  mkPainting' (dep; extraDeps) d ->
  dep.(_painting'') (dep.(_restrFrame') q Hq ε d).

Fixpoint RestrPaintingTypes' {p}:
  forall `{deps: FormDeps p n}
  (extraDeps: FormDepsExtension deps), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun n deps extraDeps =>
    { R: RestrPaintingTypes' (n := n.+1) (deps.(2); extraDeps) &T
      RestrPaintingType' (p := p) deps.(2) extraDeps }
  end.

(** Under previous assumptions, and, additionally:
      [restrPainting(p+n,0);...;restrPainting(p+n,p-1)]
    we mutually build the pair of:
    - the list of types for [cohFrame(p+1+n,0);...;cohFrame(p+1+n,p-1)]
    - definitions of [restrFrame(p+1+n,0);...;restrFrame(p+1+n,p)] *)

#[local]
Instance mkCohFrameTypesAndRestrFrames:
  forall `(deps: FormDeps p n)
  (extraDeps: FormDepsExtension deps)
  (restrPaintings': RestrPaintingTypes' extraDeps), CohFrameTypeBlock :=
  fix mkCohFrameTypesAndRestrFrames {p}:
  forall `(deps: FormDeps p n)
    (extraDeps: FormDepsExtension deps)
    (restrPaintings': RestrPaintingTypes' extraDeps), CohFrameTypeBlock :=
  match p with
  | 0 =>
    fun n deps extraDeps restrPaintings' =>
    {|
      CohFrameTypesDef := unit;
      RestrFramesDef _ := (tt; fun _ _ _ _ => tt):
        mkRestrFrameTypes deps extraDeps
    |}
  | S p =>
    fun n deps extraDeps restrPaintings' =>
    let restrFrames := (mkCohFrameTypesAndRestrFrames deps.(1)
    (deps.(2); extraDeps)%extradeps restrPaintings'.1).(RestrFramesDef) in
    let cohFrameTypes := (mkCohFrameTypesAndRestrFrames deps.(1)
    (deps.(2); extraDeps)%extradeps restrPaintings'.1).(CohFrameTypesDef) in
    {|
      CohFrameTypesDef := { Q: cohFrameTypes &T
        (* statement of cohFrameType(n+2,p) *)
        forall r q (Hrq: r <= q) (Hq: q <= n) (ε ω: arity) d,
        deps.(_restrFrames').2 q Hq ε
          ((restrFrames Q).2 r (Hrq ↕ (↑ Hq)) ω d) =
        deps.(_restrFrames').2 r (Hrq ↕ Hq) ω
          ((restrFrames Q).2 q.+1 (⇑ Hq) ε d) };
      RestrFramesDef Q :=
      (* RestrFrame(n+2,p+1) *)
      let restrFrame q (Hq: q <= n) ε
        (d: mkFrame (deps.(2); extraDeps) (restrFrames Q.1)) :=
          ((restrFrames Q.1).2 q.+1 (⇑ Hq) ε d.1 as rf in _;
           fun ω => rew [deps.(_paintings'').2] Q.2 0 q leY_O Hq ε ω d.1 in
            restrPaintings'.2 q _ ε _
              (rew unfoldPaintingProj (deps.(2); extraDeps) _ in d.2 ω)
           in forall ω,
            deps.(_paintings'').2 (deps.(_restrFrames').2  _ _ _ rf))
      in (restrFrames Q.1 as rf in _; restrFrame in forall q Hq ω,
            (mkFrame (deps.(2); extraDeps)%extradeps rf) -> _)
           : mkRestrFrameTypes deps extraDeps
    |}
  end.

(* Example: if p := 0, extraDeps := ([],E')
   mkCohFrameTypes := [] *)

Definition mkCohFrameTypes `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  (restrPaintings': RestrPaintingTypes' extraDeps) :=
  (mkCohFrameTypesAndRestrFrames deps extraDeps
    restrPaintings').(CohFrameTypesDef).

Definition mkRestrFrames `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  (restrPaintings': RestrPaintingTypes' extraDeps) :=
  (mkCohFrameTypesAndRestrFrames deps extraDeps
    restrPaintings').(RestrFramesDef).

(* Tying the loop: we type mkRestrFrame((p+1)+n,p) knowing mkRestrFrames(p+(1+n),0..p-1)
    Note that even if mkRestrFrames((p+1)+n,p) : mkRestrFrameTypes((p+1)+n,p),
    we don't have mkRestrFrame((p+1)+n,p): mkRestrFrameType((p+1)+n,p), because
    mkRestrFrameType((p+1)+n,p) assumes restrFrames((p+1)+n,0..p) which would be
    circular.
    Instead, we only require restrFrames(p+(1+n),0..p-1) then build the type of
    restrFrame(p+1+n,p) as: Frame(p+(1+n),p) -> Frame(p+n,p)
    At the end, with only the addition of restrPaintings' and cohs, the loop is gone *)

Definition mkRestrFrame `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  (restrPaintings': RestrPaintingTypes' extraDeps) cohs:
  forall q {Hq: q <= n} ε,
    mkPrevFrame extraDeps (mkRestrFrames restrPaintings' cohs) ->
    mkFrame' deps := (mkRestrFrames restrPaintings' cohs).2.

(* Example: if p := 0, extraDeps := ([],E'), restrPaintings' := , cohs := []
   then mkFullDeps := {_frames'':=[unit];_paintings'':=[E']};_restrFrames':=[\qω().()]}
   (where _restrFrames' is presented as a dependent pair, i.e. ((),\qω().()) *)

Definition mkFullDeps `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  (restrPaintings': RestrPaintingTypes' extraDeps)
  (cohs: mkCohFrameTypes restrPaintings') :=
  mkDeps extraDeps (mkRestrFrames restrPaintings' cohs).

Definition mkCohFrameType `{deps: FormDeps p n.+1}
  {dep: FormDep deps}
  {extraDeps: FormDepsExtension (deps; dep)}
  {restrFrames: mkRestrFrameTypes deps (dep; extraDeps)}
  (restrPaintings': RestrPaintingTypes' (dep; extraDeps)) :=
  forall r q (Hrq: r <= q) (Hq: q <= n) (ε ω: arity) d,
    dep.(_restrFrame') q Hq ε (restrFrames.2 r (Hrq ↕ (↑ Hq)) ω d)
    = dep.(_restrFrame') r (Hrq ↕ Hq) ω (restrFrames.2 q.+1 (⇑ Hq) ε d).

Inductive CohFramesExtension {p}: forall `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps},
  mkCohFrameTypes restrPaintings' -> Type :=
| TopCohFrame
    {deps: FormDeps p 0}
    {E': mkFrame' deps -> HSet}
    {restrPaintings': RestrPaintingTypes' (TopRestrFrames E')}
    {cohs: mkCohFrameTypes restrPaintings'}
    (E: mkFrame (TopRestrFrames E')
      (mkRestrFrames restrPaintings' cohs) -> HSet)
    : CohFramesExtension cohs
| AddCohFrame {n deps dep extraDeps}
    {restrPaintings': RestrPaintingTypes' (dep; extraDeps)}
    {restrPainting': RestrPaintingType' dep extraDeps}
    {cohs: mkCohFrameTypes restrPaintings'}
    (coh: mkCohFrameType restrPaintings'):
    CohFramesExtension (deps := (deps; dep))
      (restrPaintings' := (restrPaintings'; restrPainting')) (cohs; coh) ->
      CohFramesExtension (n := n.+1) cohs.

Declare Scope extra_cohs_scope.
Delimit Scope extra_cohs_scope with extracohs.
Bind Scope extra_cohs_scope with CohFramesExtension.
Notation "( x ; y )" := (AddCohFrame x y)
  (at level 0, format "( x ; y )"): extra_cohs_scope.

Fixpoint mkExtraDeps `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  {cohs: mkCohFrameTypes restrPaintings'}
  (extraCohs: CohFramesExtension cohs):
  FormDepsExtension (mkFullDeps restrPaintings' cohs).
Proof.
  destruct extraCohs.
  - now constructor.
  - unshelve econstructor.
    + now exact (mkFullDeps (extraDeps := extraDeps)
        (restrPaintings'; restrPainting') (cohs; coh)).(2).
    + now exact (mkExtraDeps p.+1 n (deps; dep)%deps extraDeps
        (restrPaintings'; restrPainting') (cohs; coh) extraCohs).
Defined.

Definition mkPainting `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  {cohs: mkCohFrameTypes restrPaintings'}
  (extraCohs: CohFramesExtension cohs) :=
  mkPainting' (mkExtraDeps extraCohs):
  mkFrame (p := p) extraDeps _ -> HSet.

Definition mkPrevPainting `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  {cohs: mkCohFrameTypes restrPaintings'}
  (extraCohs: CohFramesExtension cohs) :=
  mkPainting'
    ((mkFullDeps restrPaintings' cohs).(2);
      mkExtraDeps extraCohs)%extradeps:
    mkPrevFrame (p := p) extraDeps (mkRestrFrames restrPaintings' cohs) -> HSet.

(* Note: we could type mkRestrPainting(p+1+n,p) of type
   RestrPaintingType(p+1+n,p) up to using unfoldPaintingProj at other places.
   It is more convenient to refer to mkPrevPainting to later state cohPainting *)

Fixpoint mkRestrPainting `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  (cohs: mkCohFrameTypes restrPaintings')
  (extraCohs: CohFramesExtension cohs):
  forall q {Hq: q <= n} ε
    (d: mkPrevFrame extraDeps (mkRestrFrames restrPaintings' cohs)),
    mkPrevPainting extraCohs d ->
    mkPainting' extraDeps (mkRestrFrame restrPaintings' cohs q ε d).
Proof.
  intros * (l, c). destruct extraCohs, q.
  - now exact (rew unfoldPaintingProj _ _ in l ε).
  - exfalso. now apply leY_O_contra in Hq.
  - now exact (rew unfoldPaintingProj _ _ in l ε).
  - unshelve esplit.
    + intro ω. rewrite <- coh with (Hrq := leY_O) (Hq := ⇓ Hq).
      apply restrPainting'. simpl in l.
      now exact (rew unfoldPaintingProj _ _ in l ω).
    + now exact (mkRestrPainting _ _ _ extraDeps
        (restrPaintings';restrPainting') (cohs; coh) _ q (⇓ Hq) ε
        (d as x in _; l in _) c).
Defined.

Definition mkRestrPaintingTypes `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  (cohs: mkCohFrameTypes restrPaintings')
  (extraCohs: CohFramesExtension cohs) :=
  RestrPaintingTypes' (mkExtraDeps extraCohs).

Fixpoint mkRestrPaintings `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  (cohs: mkCohFrameTypes restrPaintings')
  (extraCohs: CohFramesExtension cohs):
  mkRestrPaintingTypes cohs extraCohs.
Proof.
  destruct p.
  - unshelve esplit. now exact tt.
    red; intros * c.
    now apply (mkRestrPainting cohs extraCohs q ε), c.
  - unshelve esplit. now apply (mkRestrPaintings p n.+1 _ _ _ cohs.1
      (cohs.2; extraCohs)%extracohs).
    red; intros * c. now apply (mkRestrPainting cohs extraCohs), c.
Defined.

Definition mkCohPaintingType `{deps: FormDeps p n.+1}
  {dep: FormDep deps}
  {extraDeps: FormDepsExtension (deps; dep)}
  {restrPaintings': RestrPaintingTypes' (dep; extraDeps)}
  {restrPainting': RestrPaintingType' dep extraDeps}
  {cohs: mkCohFrameTypes restrPaintings'}
  {coh: mkCohFrameType restrPaintings'}
  (extraCohs: CohFramesExtension (deps := (deps; dep))
    (restrPaintings' := (restrPaintings'; restrPainting'))
    (cohs; coh)) :=
  forall r q (Hrq: r <= q) (Hq: q <= n) (ε ω: arity)
    (d: mkPrevFrame (dep; extraDeps) (mkRestrFrames restrPaintings' cohs))
    (c: mkPrevPainting (coh; extraCohs) d),
  rew [dep.(_painting'')] coh r q Hrq Hq ε ω d in
  restrPainting' q _ ε _ (mkRestrPainting cohs (coh; extraCohs) r ω d c) =
  restrPainting' r _ ω _ (mkRestrPainting cohs (coh; extraCohs) q.+1 ε d c).

Fixpoint mkCohPaintingTypes {p}:
  forall `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  {cohs: mkCohFrameTypes restrPaintings'}
  (extraCohs: CohFramesExtension cohs),
  Type :=
  match p with
  | 0 => fun _ _ _ _ _ _ => unit
  | S p =>
    fun n deps extraDeps restrPaintings' cohs extraCohs =>
    { R: mkCohPaintingTypes (cohs.2; extraCohs) &T
         mkCohPaintingType extraCohs }
  end.

(* Fixpoint mkCohFrame `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  (cohs: mkCohFrameTypes restrPaintings')
  (extraCohs: CohFramesExtension cohs)
  (cohPaintings: mkCohPaintingTypes extraCohs):
  mkCohFrameType (dep := (mkFullDeps restrPaintings' cohs).(2))
    (mkRestrPaintings cohs extraCohs). *)

Axiom F: False.

Fixpoint mkCohFrames `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  (cohs: mkCohFrameTypes restrPaintings')
  (extraCohs: CohFramesExtension cohs)
  (cohPaintings: mkCohPaintingTypes extraCohs)
  {struct p}:
  mkCohFrameTypes (mkRestrPaintings cohs extraCohs).
Proof.
  destruct p.
  - red; simpl. unshelve esplit. now exact tt. now intros.
  - unshelve esplit.
    + now apply (mkCohFrames p _ _ _ restrPaintings'.1 cohs.1
      (cohs.2; extraCohs)%extracohs cohPaintings.1).
    + intros. unshelve eapply eq_existT_curried.
      * now apply ((mkCohFrames p _ _ _ restrPaintings'.1 cohs.1
        (cohs.2; extraCohs)%extracohs cohPaintings.1).2 r.+1 q.+1
        (⇑ Hrq) _ ε ω).
      * (* prove a reorganization of the cohFrame using UIP *)
        (* then: apply (cohPaintings.2 r q _ _ ε ω). *)
        now elim F.
Defined.

Inductive CohPaintingsExtension {p}: forall `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  {cohs: mkCohFrameTypes restrPaintings'}
  {extraCohs: CohFramesExtension cohs},
  mkCohPaintingTypes extraCohs -> Type :=
| TopCohPainting
    {deps: FormDeps p 0}
    {E': mkFrame' deps -> HSet}
    {restrPaintings'}
    {cohs: mkCohFrameTypes restrPaintings'}
    {extraCohs: CohFramesExtension cohs}
    {E: mkFrame (TopRestrFrames E')
      (mkRestrFrames restrPaintings' cohs) -> HSet}
    {cohPaintings: mkCohPaintingTypes (TopCohFrame E)}
    {NextE: mkFrame (TopRestrFrames E)
       (mkRestrFrames (mkRestrPaintings cohs (TopCohFrame E))
          (mkCohFrames cohs (TopCohFrame E) cohPaintings)) -> HSet}
    : CohPaintingsExtension cohPaintings
| AddCohPainting {n deps dep extraDeps}
    {restrPaintings': RestrPaintingTypes' (dep; extraDeps)}
    {restrPainting': RestrPaintingType' dep extraDeps}
    {cohs: mkCohFrameTypes restrPaintings'}
    {coh: mkCohFrameType restrPaintings'}
    {extraCohs: CohFramesExtension (extraDeps := extraDeps)
      (restrPaintings' := (restrPaintings'; restrPainting')) (cohs; coh)}
    (cohPaintings: mkCohPaintingTypes (extraDeps := (dep; extraDeps))
      (restrPaintings' := restrPaintings') (coh; extraCohs))
    (cohPainting: mkCohPaintingType (extraDeps := extraDeps)
      (restrPaintings' := restrPaintings')
      (restrPainting' := restrPainting') extraCohs):
    CohPaintingsExtension (deps := (deps; dep))
      (restrPaintings' := (restrPaintings'; restrPainting'))
      (cohs := (cohs; coh))
      (extraCohs := extraCohs) (cohPaintings; cohPainting) ->
      CohPaintingsExtension (n := n.+1) cohPaintings.

Declare Scope extra_cohps_scope.
Delimit Scope extra_cohps_scope with extracohps.
Bind Scope extra_cohps_scope with CohPaintingsExtension.
Notation "( x ; y )" := (AddCohPainting _ x y)
  (at level 0, format "( x ; y )"): extra_cohps_scope.

Fixpoint mkExtraCohs `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  {cohs: mkCohFrameTypes restrPaintings'}
  (extraCohs: CohFramesExtension cohs)
  {cohPaintings: mkCohPaintingTypes extraCohs}
  (extraCohPaintings: CohPaintingsExtension cohPaintings):
  CohFramesExtension (mkCohFrames cohs extraCohs cohPaintings).
Proof.
  destruct extraCohPaintings.
  - constructor. apply NextE.
  - unshelve econstructor.
    + now exact (mkRestrPaintings (extraDeps := extraDeps)
        (restrPaintings' := (restrPaintings'; restrPainting'))
        (cohs; coh) extraCohs).2.
    + red; intros.
      now exact ((mkCohFrames (deps := (deps; dep))
        (restrPaintings' := (restrPaintings'; restrPainting'))
        (cohs; coh) extraCohs (cohPaintings; cohPainting)).2 r q Hrq Hq ε ω d).
    + now exact (mkExtraCohs p.+1 n (deps; dep)%deps extraDeps
        (restrPaintings'; restrPainting') (cohs; coh) extraCohs
        (cohPaintings; cohPainting) extraCohPaintings).
Defined.

Fixpoint mkCohPainting `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  {cohs: mkCohFrameTypes restrPaintings'}
  (extraCohs: CohFramesExtension cohs)
  {cohPaintings: mkCohPaintingTypes extraCohs}
  (extraCohPaintings: CohPaintingsExtension cohPaintings):
  mkCohPaintingType (dep := (mkFullDeps restrPaintings' cohs).(2))
    (mkExtraCohs extraCohs extraCohPaintings).
Proof.
  red; intros. destruct extraCohPaintings.
  - admit.
  - admit.
Admitted.

Fixpoint mkCohPaintings `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  {cohs: mkCohFrameTypes restrPaintings'}
  (extraCohs: CohFramesExtension cohs)
  {cohPaintings: mkCohPaintingTypes extraCohs}
  (extraCohPaintings: CohPaintingsExtension cohPaintings) {struct p}:
  mkCohPaintingTypes (mkExtraCohs extraCohs extraCohPaintings).
Proof.
  destruct p.
  - unshelve esplit. now exact tt.
    red; intros *. now apply (mkCohPainting extraCohs extraCohPaintings).
  - unshelve esplit. now apply (mkCohPaintings p n.+1 _ _ _ cohs.1
      (cohs.2; extraCohs)%extracohs cohPaintings.1
      (cohPaintings.2; extraCohPaintings)%extracohps).
    red; intros *. now apply (mkCohPainting extraCohs extraCohPaintings).
Defined.

Class νTypeAux p := {
  deps: FormDeps p 0;
  restrPaintings' E': RestrPaintingTypes' (TopRestrFrames E');
  cohFrames E': mkCohFrameTypes (restrPaintings' E');
  cohPaintings E' E : mkCohPaintingTypes (cohs := cohFrames E')
    (TopCohFrame E);
}.

Class νType p := {
  prefix'': Type;
  data: prefix'' -> νTypeAux p;
}.

(***************************************************)
(** The construction of [νType n+1] from [νType n] *)

(** Extending the initial prefix *)
Definition mkPrefix'' p {C: νType p}: Type :=
  { D: C.(prefix'') &T mkFrame' (n := 0) (C.(data) D).(deps) -> HSet }.

Section νTypeData.
Variable p: nat.
Variable C: νType p.
Variable D: mkPrefix'' p.

Definition mkDeps': FormDeps p.+1 0 :=
  mkFullDeps _ ((C.(data) D.1).(cohFrames) D.2).

Definition mkRestrPaintings' E': RestrPaintingTypes' _ :=
  mkRestrPaintings ((C.(data) D.1).(cohFrames) D.2) (TopCohFrame E').

Definition mkCohFrames' E': mkCohFrameTypes (mkRestrPaintings' E') :=
  mkCohFrames ((C.(data) D.1).(cohFrames) D.2)
   (TopCohFrame E') ((C.(data) D.1).(cohPaintings) D.2 E').

Definition mkCohPaintings' E' E:
  mkCohPaintingTypes (cohs := mkCohFrames' E') (TopCohFrame _) :=
 mkCohPaintings (TopCohFrame E') (TopCohPainting (NextE := E)
  (extraCohs := TopCohFrame E')).

End νTypeData.

#[local]
Instance mkνType p {C: νType p}: νType p.+1.
  unshelve esplit.
  now exact (mkPrefix'' p).
  intro D. unshelve esplit.
  now eapply mkDeps'.
  now apply mkRestrPaintings'.
  now apply mkCohFrames'.
  now apply mkCohPaintings'.
Defined.

End νType.
