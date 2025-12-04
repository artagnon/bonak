From Stdlib Require Import Logic.FunctionalExtensionality.
Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet LeYoneda Notation.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Set Typeclasses Depth 10.
Remove Printing Let sigT.
Remove Printing Let prod.

Section νSet.
Variable arity: HSet.

(** The type of lists [frame(n,0);...;frame(n,p-1)] for arbitrary k := n-p
    (the non-mandatory dependency in k is useful for type inference) *)

Fixpoint mkFrameTypes p k: Type :=
  match p with
  | 0 => unit
  | S p => { frames: mkFrameTypes p k.+1 &T HSet }
  end.

(** The type of lists [painting(n,0);...;painting(n,p-1)] for arbitrary n *)

Fixpoint mkPaintingTypes p k: mkFrameTypes p k -> Type :=
  match p with
  | 0 => fun _ => unit
  | S p => fun frames =>
    { paintings: mkPaintingTypes p k.+1 frames.1 &T frames.2 -> HSet }
  end.

(** A helper type so as to mutually build the types of restrFrames and
    the body of frames using a single fixpoint *)

Class RestrFrameTypeBlock p k := {
  RestrFrameTypesDef: Type;
  FrameDef: RestrFrameTypesDef -> mkFrameTypes p.+1 k;
}.

(**
For n and p<=n be given, and assuming [frame(n,0);...;frame(n,p)] and
[painting(n,0);...;painting(n,p)], we build the list of pairs:
- of the types RestrFrameTypes(n,p) of the list
  [restrFrame(n,0);...;restrFrame(n,p-1)]
  (represented as an inhabitant of a sigma-type
   {R:RestrFrameTypes(n,0) & ... & RestrFrameTypes(n,p-1)})
- and of the list [frame(n+1,0);...;frame(n+1,p)] in function of effective
  restrFrames of type RestrFrameTypes(n,p)

That is, we build:
  p = 0 : { RestrFrameTypes(n,0..0-1) := unit ;
                  (which denotes the empty list of restrFrameTypes)
            Frames(n+1,0..0)(restrFrames^n_{0..0-1}) := [unit]
                  (representing lists by Sigma-types) }
  p = 1 : { RestrFrameTypes(n,0..0) = {_:unit & restrFrameType(n,0)} ;
                  (thus denoting the singleton list [restrFrameType(n,0])
            Frames(n+1,0..1)(restrFrames(n,0..0) :=
                  [unit;{d:Frame(n,0)&Painting(n,0)(restrFrame(n,0)(d)}] }
  ...
  p     : { RestrFrameTypes(n,0..p-1) =
              {RestrFrameType(n,0) & ... & RestrFrameType(n,p-1)} ;
            Frames(n+1,0..p)(restrFrames(n,0..p-1)) :=
              [frame(n+1,0);...;frame(n+1,p)] }

  In practise, it is convenient to work with the difference k := n-p
  rather than n itself. So, below, k is the difference.
*)

Generalizable Variables p k frames.

Definition mkRestrFrameTypesStep `(frames: mkFrameTypes p.+1 k)
  (prev: RestrFrameTypeBlock p k.+1) :=
  { R: prev.(RestrFrameTypesDef) &T
    forall q (Hq: q <= k) (ε: arity), (prev.(FrameDef) R).2 -> frames.2 }.

Definition mkLayer `{paintings: mkPaintingTypes p.+1 k frames}
  {prev: RestrFrameTypeBlock p k.+1}
  (restrFrames: mkRestrFrameTypesStep frames prev)
  (d: (prev.(FrameDef) restrFrames.1).2) :=
  hforall ε, paintings.2 (restrFrames.2 0 leY_O ε d).

Fixpoint mkRestrFrameTypesAndFrames {p k}:
  forall `(paintings: mkPaintingTypes p k frames), RestrFrameTypeBlock p k :=
  match p with
  | 0 => fun frames paintings =>
    {|
      RestrFrameTypesDef := unit;
      FrameDef _ := (tt; hunit): mkFrameTypes 1 k
    |}
  | p.+1 => fun frames paintings =>
    let prev :=
      mkRestrFrameTypesAndFrames paintings.1 in
    let frames' := prev.(FrameDef) in
    {|
      RestrFrameTypesDef := mkRestrFrameTypesStep frames prev;
      FrameDef R :=
        (frames' R.1; { d: (frames' R.1).2 &
          mkLayer (paintings := paintings) R d }): mkFrameTypes p.+2 k
    |}
  end.

Definition mkRestrFrameTypes `(paintings: mkPaintingTypes p k frames) :=
  (mkRestrFrameTypesAndFrames paintings).(RestrFrameTypesDef).

Class DepsRestr p k := {
  _frames: mkFrameTypes p k;
  _paintings: mkPaintingTypes p k _frames;
  _restrFrames: mkRestrFrameTypes _paintings;
}.

Definition mkFrames `(deps: DepsRestr p k): mkFrameTypes p.+1 k :=
  (mkRestrFrameTypesAndFrames
    deps.(_paintings)).(FrameDef) deps.(_restrFrames).

Definition mkFrame `(deps: DepsRestr p k): HSet := (mkFrames deps).2.

Class DepRestr `(deps: DepsRestr p k.+1) := {
  _frame: HSet;
  _painting: _frame -> HSet;
  _restrFrame: forall q {Hq: q <= k} (ε: arity), mkFrame deps -> _frame;
}.

#[local]
Instance proj1Deps `(deps: DepsRestr p.+1 k): DepsRestr p k.+1 :=
{|
  _frames := deps.(_frames).1;
  _paintings := deps.(_paintings).1;
  _restrFrames := deps.(_restrFrames).1;
|}.

Declare Scope depsrestr_scope.
Delimit Scope depsrestr_scope with depsrestr.
Bind Scope depsrestr_scope with DepsRestr.

Notation "x .(1)" := (proj1Deps x%_depsrestr)
  (at level 1, left associativity, format "x .(1)"): depsrestr_scope.

Inductive DepsRestrExtension p: forall k, DepsRestr p k -> Type :=
| TopRestrDep {deps}:
  forall E: mkFrame deps -> HSet, DepsRestrExtension p 0 deps
| AddRestrDep {k} deps:
  DepsRestrExtension p.+1 k deps -> DepsRestrExtension p k.+1 deps.(1).

Arguments TopRestrDep {p deps}.
Arguments AddRestrDep {p k} deps.

Declare Scope extra_deps_scope.
Delimit Scope extra_deps_scope with extradeps.
Bind Scope extra_deps_scope with DepsRestrExtension.
Notation "( x ; y )" := (AddRestrDep x y)
  (at level 0, format "( x ; y )"): extra_deps_scope.

(* Example: if p := 0, extraDeps := ([],E) mkPainting:= [E] *)

Generalizable Variables deps.

Fixpoint mkPainting `(extraDeps: DepsRestrExtension p k deps):
  mkFrame deps -> HSet :=
  match extraDeps with
  | TopRestrDep E => fun d => E d
  | AddRestrDep deps extraDeps => fun (d: mkFrame deps.(1)) =>
      {l: mkLayer deps.(_restrFrames) d & mkPainting extraDeps (d; l)}
  end.

Fixpoint mkPaintings {p k}: forall `(extraDeps: DepsRestrExtension p k deps),
  mkPaintingTypes p.+1 k (mkFrames deps) :=
  match p with
  | 0 => fun deps extraDeps => (tt; mkPainting extraDeps)
  | S p => fun deps extraDeps =>
    (mkPaintings (deps; extraDeps)%extradeps; mkPainting extraDeps)
  end.

Lemma unfoldPaintingProj `{extraDeps: DepsRestrExtension p k deps}
  {d: mkFrame deps}: mkPainting extraDeps d = (mkPaintings extraDeps).2 d.
Proof.
  now destruct p.
Defined.

(** We combine mkFrames (that is frames(n+1,p)),
    mkPaintings (that is paintings(n+1,p)) and an assumed restrFrames
    (that is restrFrames(n+1,p)) to build "dependencies" at the next
    level, that is a deps(n+1,p).
    That is, from:
       [frame(n,0);...;frame(n,p-1)]
       [painting(n,0);...;painting(n,p-1)]
       [restrFrame(n,0);...;restrFrame(n,p-1)] for p<=n+1
     (forming a "deps"), and
       [frame(n,p);...;frame(n,n]
       [painting(n,p);...;painting(n,n)]
       [restrFrame(n,p);...;restrFrame(n,n)]
       E:frame(n+1,n+1) -> HSet
     (forming an "extraDeps"), and
       [restrFrame(n+1,0);...;restrFrame(n+1,p)]
     (thanks to being able to form RestrFrameTypes(n+1,0..p) from deps and
      extradeps, e.g. if p := 0, extraDeps := ([],E) then
      mkRestrFrameTypes(n+1,0) := [unit -> unit])
     we form:
       [frame(n+1,0);...;frame(n+1,p)] (built by mkFrames')
       [painting(n+1,0);...;painting(p+n,p)] (built by mkPaintings')
       [restrFrame(n+1,0);...;restrFrame(n+1,p)] *)

Definition mkDepsRestr `{extraDeps: DepsRestrExtension p k deps}
  (restrFrames: mkRestrFrameTypes (mkPaintings extraDeps)) :=
{|
  _frames := mkFrames deps;
  _paintings := mkPaintings extraDeps;
  _restrFrames := restrFrames;
|}.

Definition mkRestrPaintingType
  `(extraDeps: DepsRestrExtension p.+1 k deps) :=
  forall q (Hq: q <= k) ε (d: mkFrame deps.(1)),
  (mkPaintings (deps; extraDeps)).2 d ->
  deps.(_paintings).2 (deps.(_restrFrames).2 q _ ε d).

Fixpoint mkRestrPaintingTypes {p}:
  forall `(extraDeps: DepsRestrExtension p k deps), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k deps extraDeps =>
    { _: mkRestrPaintingTypes (deps; extraDeps) &T
      mkRestrPaintingType extraDeps }
  end.

(** A helper type so as to mutually build the types of cohFrames and
    the body of restrFrames using a single fixpoint *)

Class CohFrameTypeBlock `{extraDeps: DepsRestrExtension p k deps} := {
  CohFrameTypesDef: Type;
  RestrFramesDef: CohFrameTypesDef -> mkRestrFrameTypes (mkPaintings extraDeps)
}.

(** Auxiliary definitions to mutually build cohFrameTypes and restrFrames *)

Definition mkCohFrameTypesStep `{extraDeps: DepsRestrExtension p.+1 k deps}
  {restrPaintings: mkRestrPaintingTypes extraDeps}
  (prev: CohFrameTypeBlock (extraDeps := (deps; extraDeps))): Type :=
  { Q: prev.(CohFrameTypesDef) &T
    forall r q (Hrq: r <= q) (Hq: q <= k) (ε ω: arity) d,
    deps.(_restrFrames).2 q Hq ε
      ((prev.(RestrFramesDef) Q).2 r (Hrq ↕ (↑ Hq)) ω d) =
    deps.(_restrFrames).2 r (Hrq ↕ Hq) ω
      ((prev.(RestrFramesDef) Q).2 q.+1 (⇑ Hq) ε d) }.

Definition mkRestrLayer `{extraDeps: DepsRestrExtension p.+1 k deps}
  (restrPaintings: mkRestrPaintingTypes extraDeps)
  {prev: CohFrameTypeBlock (extraDeps := (deps; extraDeps))}
  (cohFrames: mkCohFrameTypesStep (restrPaintings := restrPaintings) prev)
  q (Hq: q <= k) (ε: arity)
  (d: mkFrame (mkDepsRestr (prev.(RestrFramesDef) cohFrames.1)).(1)):
  mkLayer (prev.(RestrFramesDef) cohFrames.1) d -> mkLayer deps.(_restrFrames)
    ((prev.(RestrFramesDef) cohFrames.1).2 q.+1 (⇑ Hq) ε d) :=
  fun l ω => rew [deps.(_paintings).2] cohFrames.2 0 q leY_O Hq ε ω d in
             restrPaintings.2 q Hq ε _ (l ω).

(** Under previous assumptions, and, additionally:
      [restrPainting(n,0);...;restrPainting(n,p-1)]
    we mutually build the pair of:
    - the list of types for [cohFrame(n,0);...;cohFrame(n,p-1)]
    - definitions of [restrFrame(n+1,0);...;restrFrame(n+1,p)] *)

#[local]
Instance mkCohFrameTypesAndRestrFrames:
  forall `{extraDeps: DepsRestrExtension p k deps}
  (restrPaintings: mkRestrPaintingTypes extraDeps), CohFrameTypeBlock :=
  fix mkCohFrameTypesAndRestrFrames {p}:
  forall `(extraDeps: DepsRestrExtension p k deps)
    (restrPaintings: mkRestrPaintingTypes extraDeps), CohFrameTypeBlock :=
  match p with
  | 0 =>
    fun k deps extraDeps restrPaintings =>
    {|
      CohFrameTypesDef := unit;
      RestrFramesDef _ := (tt; fun _ _ _ _ => tt)
    |}
  | S p =>
    fun k deps extraDeps restrPaintings =>
    let prev := mkCohFrameTypesAndRestrFrames
      (deps; extraDeps)%extradeps restrPaintings.1 in
    let restrFrames := prev.(RestrFramesDef) in
    let cohFrameTypes := prev.(CohFrameTypesDef) in
    {|
      CohFrameTypesDef := mkCohFrameTypesStep prev;
      RestrFramesDef Q :=
      (* RestrFrame(n+2,p+1) *)
      let restrFrame q (Hq: q <= k) ε
        (d: mkFrame (mkDepsRestr
          (extraDeps := (deps; extraDeps)) (restrFrames Q.1))) :=
          ((restrFrames Q.1).2 q.+1 (⇑ Hq) ε d.1;
           mkRestrLayer restrPaintings Q q _ ε d.1 d.2)
      in (restrFrames Q.1; restrFrame)
    |}
  end.

(* Example: if p := 0, extraDeps := ([],E)
   mkCohFrameTypes := [] *)

Definition mkCohFrameTypes `{extraDeps: DepsRestrExtension p k deps}
  (restrPaintings: mkRestrPaintingTypes extraDeps) :=
  (mkCohFrameTypesAndRestrFrames restrPaintings).(CohFrameTypesDef).

Class DepsCohs p k := {
  _deps: DepsRestr p k;
  _extraDeps: DepsRestrExtension p k _deps;
  _restrPaintings: mkRestrPaintingTypes _extraDeps;
  _cohs: mkCohFrameTypes _restrPaintings;
}.

#[local]
Instance mkDepsCohs0 `{deps: DepsRestr p 0} {E: mkFrame deps -> HSet}
  {restrPaintings: mkRestrPaintingTypes (TopRestrDep E)}
  (cohs: mkCohFrameTypes restrPaintings): DepsCohs p 0 := {| _cohs := cohs |}.

#[local]
Instance proj1DepsCohs `(depsCohs: DepsCohs p.+1 k): DepsCohs p k.+1 :=
{|
  _deps := depsCohs.(_deps).(1);
  _extraDeps := (depsCohs.(_deps); depsCohs.(_extraDeps));
  _restrPaintings := depsCohs.(_restrPaintings).1;
  _cohs := depsCohs.(_cohs).1;
|}.

Declare Scope depscohs_scope.
Delimit Scope depscohs_scope with depscohs.
Bind Scope depscohs_scope with DepsCohs.
Notation "x .(1)" := (proj1DepsCohs x%depscohs)
  (at level 1, left associativity, format "x .(1)"): depscohs_scope.

(** The restrFrame(n+1,0..p) component of the fixpoint *)

Definition mkRestrFrames `{depsCohs: DepsCohs p k} :=
  (mkCohFrameTypesAndRestrFrames depsCohs.(_restrPaintings)).(RestrFramesDef)
    depsCohs.(_cohs).

(** Deducing restrFrame(n+1,p) *)

(** Note that we use mkRestrFrames(n+1,p) both to build frame(n+2,p) and
    restrFrame(n+1,p) : frame(n+2,p) -> frame(n+1,p), according to the
    circularity between Frames and RestrFrameTypes.
    But now, thanks to restrPaintings and cohFrames, we have an effective
    definition of RestrFrame(n+1,p) and the circular dependency of frame(n+2,p)
    with an inhabitant RestrFrame(n+1,p) of RestrFrameType(n+1,p) is gone.
 *)

Definition mkRestrFrame `{depsCohs: DepsCohs p k}:
  forall q (Hq: q <= k) (ε: arity),
  mkFrame (mkDepsRestr mkRestrFrames).(1) -> mkFrame depsCohs.(_deps) :=
  mkRestrFrames.2.

(* Example: if p := 0, extraDeps := ([],E), restrPaintings := , cohs := []
   then mkFullDepsRestr := {_frames'':=[unit];
                       _paintings'':=[E]};
                       _restrFrames':=[\qω().()]}
   (where _restrFrames' is presented as a dependent pair, i.e. ((),\qω().()) *)

Definition mkFullDepsRestr `{depsCohs: DepsCohs p k} :=
  mkDepsRestr mkRestrFrames.

Inductive DepsCohsExtension p: forall k (depsCohs: DepsCohs p k), Type :=
| TopCohDep `{depsCohs: DepsCohs p 0}
  (E: mkFrame (mkDepsRestr mkRestrFrames) -> HSet):
  DepsCohsExtension p 0 depsCohs
| AddCohDep {k} (depsCohs: DepsCohs p.+1 k):
  DepsCohsExtension p.+1 k depsCohs -> DepsCohsExtension p k.+1 depsCohs.(1).

Arguments TopCohDep {p depsCohs}.
Arguments AddCohDep {p k}.

Declare Scope extra_deps_cohs_scope.
Delimit Scope extra_deps_cohs_scope with extradepscohs.
Bind Scope extra_deps_cohs_scope with DepsCohsExtension.
Notation "( x ; y )" := (AddCohDep x y)
  (at level 0, format "( x ; y )"): extra_deps_cohs_scope.

Generalizable Variables depsCohs.

Fixpoint mkExtraDeps `(extraDepsCohs: DepsCohsExtension p k depsCohs):
  DepsRestrExtension p.+1 k mkFullDepsRestr.
Proof.
  destruct extraDepsCohs.
  - now constructor.
  - apply (AddRestrDep mkFullDepsRestr (mkExtraDeps p.+1 k depsCohs extraDepsCohs)).
Defined.

(* Note: We could type mkRestrPainting(n+1,p) of type
   mkRestrPaintingType(n+1,p) up to using unfoldPaintingProj at other places.
*)

Definition mkRestrPaintingType'
  `(extraDepsCohs: DepsCohsExtension p k depsCohs) :=
  forall q (Hq: q <= k) ε (d: mkFrame (mkDepsRestr mkRestrFrames).(1)),
  mkPainting (mkFullDepsRestr; mkExtraDeps extraDepsCohs)%extradeps d ->
  (mkPaintings depsCohs.(_extraDeps)).2 (mkRestrFrame q Hq ε d).

(* Note: a priori, unfoldPaintingProj can be avoided because only
   "mkRestrPaintingType 0" and "mkRestrPaintingType p.+1" are later used,
   so unfoldPaintingProj would then reduce in each cases *)

Fixpoint mkRestrPainting `(extraDepsCohs: DepsCohsExtension p k depsCohs):
  mkRestrPaintingType' extraDepsCohs.
Proof.
  red; intros * (l, c); destruct q.
  - now exact (l ε).
  - destruct extraDepsCohs.
    + exfalso; now apply leY_O_contra in Hq.
    + rewrite <- unfoldPaintingProj. unshelve esplit.
      * now exact (mkRestrLayer depsCohs.(_restrPaintings) depsCohs.(_cohs)
        q (⇓ Hq) ε d l).
      * now exact (mkRestrPainting p.+1 k depsCohs extraDepsCohs q (⇓ Hq) ε (d; l) c).
Defined.

Fixpoint mkRestrPaintings
  `(extraDepsCohs: DepsCohsExtension p k depsCohs):
  mkRestrPaintingTypes (mkExtraDeps extraDepsCohs).
Proof.
  destruct p.
  - unshelve esplit. now exact tt.
    now exact (mkRestrPainting extraDepsCohs).
  - unshelve esplit.
    now exact (mkRestrPaintings p k.+1 depsCohs.(1)%depscohs
      (depsCohs; extraDepsCohs)%extradepscohs).
    now exact (mkRestrPainting extraDepsCohs).
Defined.

Definition mkCohPaintingType
  `(extraDepsCohs: DepsCohsExtension p.+1 k depsCohs) :=
  forall r q (Hrq: r <= q) (Hq: q <= k) (ε ω: arity)
    (d: mkFrame (mkDepsRestr mkRestrFrames).(1))
    (c: (mkPaintings (mkFullDepsRestr;
      mkExtraDeps (depsCohs; extraDepsCohs))).2 d),
  rew [depsCohs.(_deps).(_paintings).2] depsCohs.(_cohs).2 r q Hrq Hq ε ω d in
  depsCohs.(_restrPaintings).2 q Hq ε _
    ((mkRestrPaintings (depsCohs; extraDepsCohs)).2 r _ ω d c) =
  depsCohs.(_restrPaintings).2 r (Hrq ↕ Hq) ω _
    ((mkRestrPaintings (depsCohs; extraDepsCohs)).2 q.+1 _ ε d c).

Fixpoint mkCohPaintingTypes {p}:
  forall `(extraDepsCohs: DepsCohsExtension p k depsCohs), Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k depsCohs extraDepsCohs =>
    { R: mkCohPaintingTypes (depsCohs; extraDepsCohs) &T
         mkCohPaintingType extraDepsCohs }
  end.

Lemma mkCoh2Frame `(extraDepsCohs: DepsCohsExtension p.+1 k depsCohs)
  (cohPaintings: mkCohPaintingTypes extraDepsCohs)
  (prevCohFrames: mkCohFrameTypes
     (extraDeps := (mkFullDepsRestr; mkExtraDeps extraDepsCohs))
     (mkRestrPaintings extraDepsCohs).1) :
  forall (r q: nat) (Hrq: r <= q) (Hq: q <= k) (ε ω: arity)
  (d : mkFrame (mkDepsRestr (mkRestrFrames (depsCohs := {| _cohs := prevCohFrames.1 |}))).(1))
  (𝛉 : arity),
  f_equal
    (fun x : mkFrame depsCohs.(_deps).(1) =>
     depsCohs.(_deps).(_restrFrames).2 q _ ε x)
    (prevCohFrames.2 0 r leY_O (Hrq ↕ ↑ Hq) ω 𝛉 d)
  • (depsCohs.(_cohs).2 0 q leY_O Hq ε 𝛉
       (((mkCohFrameTypesAndRestrFrames
            (mkRestrPaintings (depsCohs; extraDepsCohs)).1).(
         RestrFramesDef) prevCohFrames.1).2 r.+1 (⇑ (Hrq ↕ ↑ Hq)) ω d)
     • f_equal
         (fun x =>
          depsCohs.(_deps).(_restrFrames).2 0 leY_O 𝛉 x)
         (prevCohFrames.2 r.+1 q.+1 (⇑ Hrq) (⇑ Hq) ε ω d)) =
  depsCohs.(_cohs).2 r q Hrq Hq ε ω
    (((mkCohFrameTypesAndRestrFrames
         (mkRestrPaintings (depsCohs; extraDepsCohs)).1).(
      RestrFramesDef) prevCohFrames.1).2 0 leY_O 𝛉 d)
  • (f_equal
       (fun x : mkFrame depsCohs.(_deps).(1) =>
        depsCohs.(_deps).(_restrFrames).2 r _ ω x)
       (prevCohFrames.2 0 q.+1 leY_O (⇑ Hq) ε 𝛉 d)
     • depsCohs.(_cohs).2 0 r leY_O (Hrq ↕ Hq) ω 𝛉
         (((mkCohFrameTypesAndRestrFrames
              (mkRestrPaintings (depsCohs; extraDepsCohs)).1).(
           RestrFramesDef) prevCohFrames.1).2 q.+2 (⇑ (⇑ Hq)) ε d)).
Proof.
  now intros; apply depsCohs.(_deps).(_frames).2.(UIP).
Defined.

Definition mkCohLayer `{extraDepsCohs: DepsCohsExtension p.+1 k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs)
  {prevCohFrames: mkCohFrameTypes
    (extraDeps := (mkFullDepsRestr; mkExtraDeps extraDepsCohs))
    (mkRestrPaintings extraDepsCohs).1}
  r q {Hrq: r <= q} {Hq: q <= k} (ε ω: arity)
  (d: mkFrame (mkDepsRestr (mkRestrFrames (depsCohs := {| _cohs := prevCohFrames.1 |}))).(1))
  (l: mkLayer mkRestrFrames d):
  rew [mkLayer _] prevCohFrames.2 r.+1 q.+1 (⇑ Hrq) (⇑ Hq) ε ω d in
    mkRestrLayer depsCohs.(_restrPaintings) depsCohs.(_cohs) q Hq ε _
      (mkRestrLayer (mkRestrPaintings extraDepsCohs).1 _ r (Hrq ↕ ↑ Hq) ω d l) =
    mkRestrLayer depsCohs.(_restrPaintings) depsCohs.(_cohs) r (Hrq ↕ Hq) ω _
      (mkRestrLayer (mkRestrPaintings extraDepsCohs).1 _ q.+1 (⇑ Hq) ε d l).
Proof.
  apply functional_extensionality_dep; intros 𝛉.
  rewrite <- map_subst_app. unfold mkRestrLayer; simpl.
  rewrite
    <- map_subst with (f := fun x => depsCohs.(_restrPaintings).2 q Hq ε x),
    <- map_subst with
        (f := fun x => depsCohs.(_restrPaintings).2 r (Hrq ↕ Hq) ω x),
    -> rew_map with (P := fun x => depsCohs.(_deps).(_paintings).2 x)
        (f := fun x => depsCohs.(_deps).(_restrFrames).2 O leY_O 𝛉 x),
    -> rew_map with (P := fun x => depsCohs.(_deps).(_paintings).2 x)
        (f := fun x => depsCohs.(_deps).(_restrFrames).2 r
          (Hrq ↕ Hq) ω x),
    -> rew_map with (P := fun x => depsCohs.(_deps).(_paintings).2 x)
        (f := fun x => depsCohs.(_deps).(_restrFrames).2 q _ ε x),
    <- cohPaintings.2.
  repeat rewrite rew_compose.
  apply rew_swap with (P := fun x => depsCohs.(_deps).(_paintings).2 x).
  rewrite rew_app_rl. now trivial.
  now apply mkCoh2Frame.
Defined.

Fixpoint mkCohFrames `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs) {struct p}:
  mkCohFrameTypes (mkRestrPaintings extraDepsCohs).
Proof.
  destruct p.
  - unshelve esplit. now exact tt. now intros.
  - unshelve esplit.
    + now exact (mkCohFrames p k.+1 depsCohs.(1)%depscohs
      (depsCohs; extraDepsCohs)%extradepscohs cohPaintings.1).
    + intros r q Hrq Hq ε ω d. unshelve eapply eq_existT_curried.
      now exact ((mkCohFrames p k.+1 depsCohs.(1)%depscohs
        (depsCohs; extraDepsCohs)%extradepscohs
        cohPaintings.1).2 r.+1 q.+1 (⇑ Hrq) (⇑ Hq) ε ω d.1).
      now exact (mkCohLayer cohPaintings r q ε ω d.1 d.2).
Defined.

#[local]
Instance mkDepsCohs `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs): DepsCohs p.+1 k :=
{|
  _deps := mkFullDepsRestr;
  _extraDeps := mkExtraDeps extraDepsCohs;
  _restrPaintings := mkRestrPaintings extraDepsCohs;
  _cohs := mkCohFrames cohPaintings;
|}.

Inductive DepsCohs2Extension {p}:
  forall `{extraDepsCohs: DepsCohsExtension p k depsCohs},
  mkCohPaintingTypes extraDepsCohs -> Type :=
| TopCoh2Dep `{depsCohs: DepsCohs p 0}
  {E: mkFrame (mkDepsRestr mkRestrFrames) -> HSet}
  {cohPaintings: mkCohPaintingTypes (TopCohDep E)}
  (NextE: mkFrame
    (mkDepsRestr (mkRestrFrames (depsCohs := mkDepsCohs cohPaintings))) -> HSet)
  : DepsCohs2Extension cohPaintings
| AddCoh2Dep {k} `{extraDepsCohs: DepsCohsExtension p.+1 k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs):
  DepsCohs2Extension cohPaintings -> DepsCohs2Extension cohPaintings.1.

Declare Scope extra_coh2_scope.
Delimit Scope extra_coh2_scope with extradepscohs2.
Bind Scope extra_coh2_scope with DepsCohs2Extension.
Notation "( x ; y )" := (AddCoh2Dep x y)
  (at level 0, format "( x ; y )"): extra_coh2_scope.

Fixpoint mkExtraCohs `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  {cohPaintings: mkCohPaintingTypes extraDepsCohs}
  (extraCohPaintings: DepsCohs2Extension cohPaintings):
  DepsCohsExtension p.+1 k (mkDepsCohs cohPaintings).
Proof.
  destruct extraCohPaintings.
  - now constructor.
  - apply (AddCohDep (mkDepsCohs cohPaintings)).
    now exact (mkExtraCohs p.+1 k depsCohs extraDepsCohs
      cohPaintings extraCohPaintings).
Defined.

Lemma unfoldRestrPaintings
  `{extraDepsCohs: DepsCohsExtension p k depsCohs} q {Hq: q <= k} ε
  (d: mkFrame mkFullDepsRestr.(1))
  (c: (mkPaintings (mkFullDepsRestr; mkExtraDeps extraDepsCohs)).2 d):
  (mkRestrPaintings extraDepsCohs).2 q Hq ε d c =
  mkRestrPainting extraDepsCohs q Hq ε d (rew <- unfoldPaintingProj in c).
Proof.
  now destruct p.
Defined.

Fixpoint mkCohPainting
  `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  {cohPaintings: mkCohPaintingTypes extraDepsCohs}
  (extraCohPaintings: DepsCohs2Extension cohPaintings):
  mkCohPaintingType (mkExtraCohs extraCohPaintings).
Proof.
  red; intros *.
  repeat rewrite unfoldRestrPaintings; rewrite rew_opp_l.
  destruct unfoldPaintingProj, c as (l, c), r;
  unfold mkRestrLayer; simpl; try now rewrite unfoldRestrPaintings.
  - (* r = 0 *)
    destruct extraCohPaintings; simpl; rewrite unfoldRestrPaintings; reflexivity.
  - (* r = r'+1, q is necessarily q'+1 and extraDepsCohs non empty *)
    destruct q. exfalso; now apply leY_O_contra in Hrq.
    destruct extraCohPaintings. exfalso; now apply leY_O_contra in Hq.
    rewrite <- rew_permute_ll_hset with
      (P := mkPainting (depsCohs.(_deps); depsCohs.(_extraDeps))).
    apply rew_swap.
    do 2 rewrite rew_opp_l.
    unshelve eapply (rew_existT_curried
      (Q := mkPainting depsCohs.(_extraDeps))).
    now exact (mkCohLayer cohPaintings r q (Hrq := ⇓ Hrq) ε ω d l).
    now exact (mkCohPainting p.+1 k depsCohs extraDepsCohs
      cohPaintings extraCohPaintings r q (⇓ Hrq) (⇓ Hq) ε ω (d; l) c).
Defined.

Fixpoint mkCohPaintings
  `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  {cohPaintings: mkCohPaintingTypes extraDepsCohs}
  (extraCohPaintings: DepsCohs2Extension cohPaintings) {struct p}:
  mkCohPaintingTypes (mkExtraCohs extraCohPaintings).
Proof.
  destruct p.
  - unshelve esplit. now exact tt.
    now exact (mkCohPainting extraCohPaintings).
  - unshelve esplit. now exact (mkCohPaintings p k.+1
      depsCohs.(1)%depscohs (depsCohs; extraDepsCohs)%extradepscohs
      cohPaintings.1 (cohPaintings; extraCohPaintings)%extradepscohs2).
    now exact (mkCohPainting extraCohPaintings).
Defined.

Class νSetAux p := {
  deps: DepsRestr p 0;
  restrPaintings E: mkRestrPaintingTypes (TopRestrDep E);
  cohFrames E: mkCohFrameTypes (restrPaintings E);
  cohPaintings E E': mkCohPaintingTypes
    (depsCohs := mkDepsCohs0 (cohFrames E)) (TopCohDep E');
}.

Class νSet p := {
  prefix: Type;
  data: prefix -> νSetAux p;
}.

(***************************************************)
(** The construction of [νSet n+1] from [νSet n] *)

(** Extending the initial prefix *)
Definition mkPrefix p {C: νSet p}: Type :=
  { D: C.(prefix) &T mkFrame (C.(data) D).(deps) -> HSet }.

Section νSetData.
Variable p: nat.
Variable C: νSet p.
Variable D: mkPrefix p.

Definition mkDepsCohs': DepsCohs p 0 :=
  mkDepsCohs0 ((C.(data) D.1).(cohFrames) D.2).

Definition mkDepsRestr': DepsRestr p.+1 0 :=
  mkFullDepsRestr (depsCohs := mkDepsCohs').

Definition mkRestrPaintings' E: mkRestrPaintingTypes (TopRestrDep E) :=
  mkRestrPaintings (depsCohs := mkDepsCohs') (TopCohDep E).

Definition mkCohFrames' E: mkCohFrameTypes (mkRestrPaintings' E) :=
  mkCohFrames (depsCohs := mkDepsCohs')
    ((C.(data) D.1).(cohPaintings) D.2 E).

Definition mkCohPaintings' E E':
  mkCohPaintingTypes (depsCohs := mkDepsCohs0 (mkCohFrames' E))
    (TopCohDep E') :=
  mkCohPaintings (TopCoh2Dep E').

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
  prefix := mkPrefix p;
  data := fun D: mkPrefix p =>
  {|
    deps := mkDepsRestr' p C D;
    restrPaintings := mkRestrPaintings' p C D;
    cohFrames := mkCohFrames' p C D;
    cohPaintings := mkCohPaintings' p C D
  |}
|}.

(** An [νSet] truncated up to dimension [n] *)
Fixpoint νSetAt n: νSet n :=
  match n with
  | O => mkνSet0
  | n.+1 => mkνSet (νSetAt n)
  end.

CoInductive νSetFrom n (X: (νSetAt n).(prefix)): Type := cons {
  this: mkFrame ((νSetAt n).(data) X).(deps) -> HSet;
  next: νSetFrom n.+1 (X; this);
}.

(** The final construction *)
Definition νSets := νSetFrom 0 tt.

End νSet.

Definition AugmentedSemiSimplicial := νSets hunit.
Definition SemiSimplicial := νSetFrom hunit 1 (tt; fun _ => hunit).
Definition SemiCubical := νSets hbool.

(** Some examples *)

Example SemiSimplicial4 := Eval compute in (νSetAt hunit 4).(prefix _).
Print SemiSimplicial4.
