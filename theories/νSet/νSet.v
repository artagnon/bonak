From Stdlib Require Import Logic.FunctionalExtensionality.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet Notation LeSProp.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Section νSet.
Variable arity: HSet.

(** The type of lists [frame(n,0);...;frame(n,p-1)] for arbitrary k := n-p
    (the non-mandatory dependency in k is useful for type inference) *)

Fixpoint mkFrameTypes p k: Type :=
  match p with
  | 0 => unit
  | S p => { frames: mkFrameTypes p k.+1 &T HSet }
  end.

(** The type of lists [painting(n,0);...;painting(n,p-1)] for n := k+p *)

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
  hforall ε, paintings.2 (restrFrames.2 0 leR_O ε d).

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

Instance toDepsRestr `{paintings: mkPaintingTypes p k frames}
  (restrFrames: mkRestrFrameTypes paintings) : DepsRestr p k :=
  {| _restrFrames := restrFrames |}.

#[local]
Instance proj1DepsRestr `(deps: DepsRestr p.+1 k): DepsRestr p k.+1 :=
{|
  _frames := deps.(_frames).1;
  _paintings := deps.(_paintings).1;
  _restrFrames := deps.(_restrFrames).1;
|}.

Declare Scope depsrestr_scope.
Delimit Scope depsrestr_scope with depsrestr.
Bind Scope depsrestr_scope with DepsRestr.
Notation "x .(1)" := (proj1DepsRestr x%_depsrestr)
  (at level 1, left associativity, format "x .(1)"): depsrestr_scope.

Definition mkFrames `(deps: DepsRestr p k): mkFrameTypes p.+1 k :=
  (mkRestrFrameTypesAndFrames
    deps.(_paintings)).(FrameDef) deps.(_restrFrames).

Definition mkFrame `(deps: DepsRestr p k): HSet := (mkFrames deps).2.

Inductive DepsRestrExtension p: forall k, DepsRestr p k -> Type :=
| TopRestrDep {deps} (E: mkFrame deps -> HSet): DepsRestrExtension p 0 deps
| AddRestrDep {k} deps:
  DepsRestrExtension p.+1 k deps -> DepsRestrExtension p k.+1 deps.(1).

Arguments TopRestrDep {p deps}.
Arguments AddRestrDep {p k} deps.

Declare Scope extra_depsrestr_scope.
Delimit Scope extra_depsrestr_scope with extradepsrestr.
Bind Scope extra_depsrestr_scope with DepsRestrExtension.
Notation "( x ; y )" := (AddRestrDep x y)
  (at level 0, format "( x ; y )"): extra_depsrestr_scope.

(* Example: if p := 0, extraDeps := ([],E) mkPainting:= [E] *)

Generalizable Variables deps.

Fixpoint mkPainting `(extraDeps: DepsRestrExtension p k deps):
  mkFrame deps -> HSet :=
  match extraDeps with
  | TopRestrDep E => fun d => E d
  | AddRestrDep deps extraDeps => fun (d: mkFrame deps.(1)) =>
      {l: mkLayer deps.(_restrFrames) d & mkPainting extraDeps (d; l)}
  end.

Fixpoint mkPaintingsPrefix {p k}:
  forall `(extraDeps: DepsRestrExtension p k deps),
    mkPaintingTypes p k.+1 (mkFrames deps).1 :=
  match p with
  | 0 => fun _ _ => tt
  | S p => fun deps extraDeps =>
      (mkPaintingsPrefix (deps; extraDeps)%extradepsrestr;
       mkPainting (deps; extraDeps)%extradepsrestr)
  end.

Definition mkPaintings {p k}: forall `(extraDeps: DepsRestrExtension p k deps),
  mkPaintingTypes p.+1 k (mkFrames deps) :=
  fun deps extraDeps => (mkPaintingsPrefix extraDeps; mkPainting extraDeps).

Definition mkRestrPaintingType
  `(extraDeps: DepsRestrExtension p.+1 k deps) :=
  forall q (Hq: q <= k) ε (d: mkFrame deps.(1)),
  (mkPaintings (deps; extraDeps)).2 d ->
  deps.(_paintings).2 (deps.(_restrFrames).2 q Hq ε d).

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
  (cohFrames: mkCohFrameTypesStep prev)
  q (Hq: q <= k) (ε: arity)
  (d: mkFrame (toDepsRestr (prev.(RestrFramesDef) cohFrames.1)).(1)):
  mkLayer (prev.(RestrFramesDef) cohFrames.1) d -> mkLayer deps.(_restrFrames)
    ((prev.(RestrFramesDef) cohFrames.1).2 q.+1 (⇑ Hq) ε d) :=
  fun l ω => rew [deps.(_paintings).2] cohFrames.2 0 q leR_O Hq ε ω d in
             restrPaintings.2 q Hq ε _ (l ω).

(** Under previous assumptions, and, additionally:
      [restrPainting(n,0);...;restrPainting(n,p-1)]
    we mutually build the pair of:
    - the list of types for [cohFrame(n,0);...;cohFrame(n,p-1)]
    - definitions of [restrFrame(n+1,0);...;restrFrame(n+1,p)] *)

Fixpoint mkCohFrameTypesAndRestrFrames {p k}:
  forall `{extraDeps: DepsRestrExtension p k deps}
  (restrPaintings: mkRestrPaintingTypes extraDeps), CohFrameTypeBlock :=
  match p with
  | 0 =>
    fun deps extraDeps restrPaintings =>
    {|
      CohFrameTypesDef := unit;
      RestrFramesDef _ := (tt; fun _ _ _ _ => tt)
    |}
  | S p =>
    fun deps extraDeps restrPaintings =>
    let prev := mkCohFrameTypesAndRestrFrames restrPaintings.1 in
    let restrFrames := prev.(RestrFramesDef) in
    {|
      CohFrameTypesDef := mkCohFrameTypesStep prev;
      RestrFramesDef Q :=
      let restrFrame q (Hq: q <= k) ε
        (d: mkFrame (toDepsRestr (restrFrames Q.1))) :=
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
Instance toDepsCohs `{extraDeps: DepsRestrExtension p k deps}
  {restrPaintings: mkRestrPaintingTypes extraDeps}
  (cohs: mkCohFrameTypes restrPaintings): DepsCohs p k :=
  {| _cohs := cohs |}.

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

(** For n=p+k, we combine mkFrames (that is frames(n+1,p)),
    mkPaintings (that is paintings(n+1,p)) and restrFrames
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
     (forming an "extraDeps")
     we form:
       [frame(n+1,0);...;frame(n+1,p)] (built by mkFrames)
       [painting(n+1,0);...;painting(p+n,p)] (built by mkPaintings)
       [restrFrame(n+1,0);...;restrFrame(n+1,p)] (built by mkRestrFrames)

   Example: if p := 0, extraDeps := ([],E), restrPaintings := [], cohs := []
   then mkDepsRestr := {_frames'':=[unit];
                        _paintings'':=[E]};
                        _restrFrames':=[\qω().()]}
   (where _restrFrames' is presented as a dependent pair, i.e. ((),\qω().()) *)

Definition mkDepsRestr `{depsCohs: DepsCohs p k} :=
  toDepsRestr mkRestrFrames.

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
  mkFrame mkDepsRestr.(1) -> mkFrame depsCohs.(_deps) :=
  mkRestrFrames.2.

Inductive DepsCohsExtension p: forall k (depsCohs: DepsCohs p k), Type :=
| TopCohDep `{depsCohs: DepsCohs p 0}
  (E: mkFrame mkDepsRestr -> HSet):
  DepsCohsExtension p 0 depsCohs
| AddCohDep {k} (depsCohs: DepsCohs p.+1 k):
  DepsCohsExtension p.+1 k depsCohs -> DepsCohsExtension p k.+1 depsCohs.(1).

Arguments TopCohDep {p depsCohs}.
Arguments AddCohDep {p k}.

Declare Scope extra_depscohs_scope.
Delimit Scope extra_depscohs_scope with extradepscohs.
Bind Scope extra_depscohs_scope with DepsCohsExtension.
Notation "( x ; y )" := (AddCohDep x y)
  (at level 0, format "( x ; y )"): extra_depscohs_scope.

Generalizable Variables depsCohs.

Fixpoint mkExtraDeps `(extraDepsCohs: DepsCohsExtension p k depsCohs):
  DepsRestrExtension p.+1 k mkDepsRestr :=
  match extraDepsCohs with
  | TopCohDep E => TopRestrDep E
  | AddCohDep k d => (mkDepsRestr; mkExtraDeps d)
  end.

Fixpoint mkRestrPainting `(extraDepsCohs: DepsCohsExtension p k depsCohs):
  mkRestrPaintingType (mkExtraDeps extraDepsCohs) :=
  fun q Hq ε d '(l; c) =>
    match q
    return
      (forall Hq : q <= k,
        mkDepsRestr.(_paintings).2 (mkDepsRestr.(_restrFrames).2 q Hq ε d))
    with
    | 0 => fun _ => l ε
    | q'.+1 => fun Hq =>
      match extraDepsCohs
      in DepsCohsExtension _ k depsCohs
      return
        (forall
          (Hq : q'.+1 <= k)
          (d : mkFrame mkDepsRestr.(1))
          (l : mkLayer mkDepsRestr.(_restrFrames) d),
          mkPainting (mkExtraDeps extraDepsCohs) (d; l) ->
          mkDepsRestr.(_paintings).2 (mkDepsRestr.(_restrFrames).2 q'.+1 Hq ε d))
      with
      | TopCohDep _ => fun Hq _ _ _ =>
        SFalse_rect (fun _ => _) (leR_O_contra Hq)
      | AddCohDep depsCohs extraDepsCohs => fun Hq d l c =>
        let restrLayer := mkRestrLayer depsCohs.(_restrPaintings) depsCohs.(_cohs) q' (⇓ Hq) ε d l in
        let restrPainting := mkRestrPainting extraDepsCohs q' (⇓ Hq) ε (d; l) c in
        (restrLayer; restrPainting)
      end Hq d l c
    end Hq.

Fixpoint mkRestrPaintingsPrefix {p k}:
  forall `(extraDepsCohs: DepsCohsExtension p k depsCohs),
  mkRestrPaintingTypes
    (mkDepsRestr; mkExtraDeps extraDepsCohs)%extradepsrestr :=
  match p with
  | 0 => fun _ _ => tt
  | S p =>
    fun depsCohs extraDepsCohs =>
      (mkRestrPaintingsPrefix (depsCohs; extraDepsCohs)%extradepscohs;
       mkRestrPainting (depsCohs; extraDepsCohs)%extradepscohs)
  end.

Definition mkRestrPaintings {p k}:
  forall `(extraDepsCohs: DepsCohsExtension p k depsCohs),
  mkRestrPaintingTypes (mkExtraDeps extraDepsCohs) :=
  fun depsCohs extraDepsCohs => (mkRestrPaintingsPrefix extraDepsCohs; mkRestrPainting extraDepsCohs).

Definition mkCohPaintingType
  `(extraDepsCohs: DepsCohsExtension p.+1 k depsCohs) :=
  forall r q (Hrq: r <= q) (Hq: q <= k) (ε ω: arity)
    (d: mkFrame mkDepsRestr.(1))
    (c: (mkPaintings (mkDepsRestr;
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
  (prevCohFrames: mkCohFrameTypes
     (extraDeps := (mkDepsRestr; mkExtraDeps extraDepsCohs))
     (mkRestrPaintings extraDepsCohs).1):
  forall (r q: nat) (Hrq: r <= q) (Hq: q <= k) (ε ω: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := toDepsCohs prevCohFrames.1)).(1))
  (𝛉: arity),
  f_equal
    (fun x => depsCohs.(_deps).(_restrFrames).2 q _ ε x)
    (prevCohFrames.2 0 r leR_O (Hrq ↕ ↑ Hq) ω 𝛉 d)
  • (depsCohs.(_cohs).2 0 q leR_O Hq ε 𝛉
      (mkRestrFrame r.+1 (⇑ (Hrq ↕ ↑ Hq)) ω d)
  • f_equal
      (fun x => depsCohs.(_deps).(_restrFrames).2 0 leR_O 𝛉 x)
      (prevCohFrames.2 r.+1 q.+1 (⇑ Hrq) (⇑ Hq) ε ω d)) =
  depsCohs.(_cohs).2 r q Hrq Hq ε ω (mkRestrFrame 0 leR_O 𝛉 d)
  • (f_equal
      (fun x => depsCohs.(_deps).(_restrFrames).2 r _ ω x)
      (prevCohFrames.2 0 q.+1 leR_O (⇑ Hq) ε 𝛉 d)
  • depsCohs.(_cohs).2 0 r leR_O (Hrq ↕ Hq) ω 𝛉
      (mkRestrFrame q.+2 (⇑ (⇑ Hq)) ε d)).
Proof.
  now intros; apply depsCohs.(_deps).(_frames).2.(UIP).
Defined.

Definition mkCohLayer `{extraDepsCohs: DepsCohsExtension p.+1 k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs)
  {prevCohFrames: mkCohFrameTypes
    (extraDeps := (mkDepsRestr; mkExtraDeps extraDepsCohs))
    (mkRestrPaintings extraDepsCohs).1}
  r q {Hrq: r <= q} {Hq: q <= k} (ε ω: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := toDepsCohs prevCohFrames.1)).(1))
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
        (f := fun x => depsCohs.(_deps).(_restrFrames).2 O leR_O 𝛉 x),
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

Class DepsCohs2 p k := {
  _depsCohs: DepsCohs p k;
  _extraDepsCohs: DepsCohsExtension p k _depsCohs;
  _cohPaintings: mkCohPaintingTypes _extraDepsCohs;
}.

#[local]
Instance toDepsCohs2 `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs): DepsCohs2 p k :=
  {| _cohPaintings := cohPaintings |}.

#[local]
Instance proj1DepsCohs2 `(depsCohs2: DepsCohs2 p.+1 k): DepsCohs2 p k.+1 :=
{|
  _depsCohs := depsCohs2.(_depsCohs).(1);
  _extraDepsCohs := (depsCohs2.(_depsCohs); depsCohs2.(_extraDepsCohs));
  _cohPaintings := depsCohs2.(_cohPaintings).1;
|}.

Declare Scope depscohs2_scope.
Delimit Scope depscohs2_scope with depscohs2.
Bind Scope depscohs2_scope with DepsCohs2.
Notation "x .(1)" := (proj1DepsCohs2 x%depscohs2)
  (at level 1, left associativity, format "x .(1)"): depscohs2_scope.

#[local]
Instance mkDepsCohs `(depsCohs2: DepsCohs2 p k): DepsCohs p.+1 k :=
{|
  _deps := mkDepsRestr;
  _extraDeps := mkExtraDeps depsCohs2.(_extraDepsCohs);
  _restrPaintings := mkRestrPaintings depsCohs2.(_extraDepsCohs);
  _cohs := mkCohFrames depsCohs2.(_cohPaintings);
|}.

Inductive DepsCohs2Extension p: forall k (depsCohs2: DepsCohs2 p k), Type :=
| TopCoh2Dep `{depsCohs2: DepsCohs2 p 0}
  (E: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs depsCohs2)) -> HSet)
  : DepsCohs2Extension p 0 depsCohs2
| AddCoh2Dep {k} (depsCohs2: DepsCohs2 p.+1 k):
  DepsCohs2Extension p.+1 k depsCohs2 ->
  DepsCohs2Extension p k.+1 depsCohs2.(1).

Arguments TopCoh2Dep {p depsCohs2}.
Arguments AddCoh2Dep {p k}.

Declare Scope extra_depscohs2_scope.
Delimit Scope extra_depscohs2_scope with extradepscohs2.
Bind Scope extra_depscohs2_scope with DepsCohs2Extension.
Notation "( x ; y )" := (AddCoh2Dep x y)
  (at level 0, format "( x ; y )"): extra_depscohs2_scope.

Fixpoint mkExtraCohs `{depsCohs2: DepsCohs2 p k}
  (extraDepsCohs2: DepsCohs2Extension p k depsCohs2):
  DepsCohsExtension p.+1 k (mkDepsCohs depsCohs2).
Proof.
  destruct extraDepsCohs2.
  - now constructor.
  - apply (AddCohDep (mkDepsCohs depsCohs2)).
    now exact (mkExtraCohs p.+1 k depsCohs2 extraDepsCohs2).
Defined.

Fixpoint mkCohPainting `{depsCohs2: DepsCohs2 p k}
  (extraDepsCohs2: DepsCohs2Extension p k depsCohs2):
  mkCohPaintingType (mkExtraCohs extraDepsCohs2).
Proof.
  red; intros *. destruct c as (l, c), r.
  - (* r = 0 *)
    destruct extraDepsCohs2, depsCohs2.
    generalize dependent _extraDepsCohs0. intro.
    now refine (match _extraDepsCohs0 with TopCohDep E => _ end).
    now reflexivity.
  - (* r = r'+1, q is necessarily q'+1 and extraDepsCohs non empty *)
    destruct q.
    { exfalso; now apply leR_O_contra in Hrq. }
    destruct extraDepsCohs2.
    { exfalso; now apply leR_O_contra in Hq. }
    simpl.
    unshelve eapply (eq_existT_curried_dep
      (Q := mkPainting depsCohs2.(_depsCohs).(_extraDeps))).
    + now exact
      (mkCohLayer depsCohs2.(_cohPaintings) r q (Hrq := ⇓ Hrq) ε ω d l).
    + now exact (mkCohPainting p.+1 k depsCohs2 extraDepsCohs2
      r q (⇓ Hrq) (⇓ Hq) ε ω (d; l) c).
Defined.

Fixpoint mkCohPaintings `{depsCohs2: DepsCohs2 p k}
  (extraDepsCohs2: DepsCohs2Extension p k depsCohs2) {struct p}:
  mkCohPaintingTypes (mkExtraCohs extraDepsCohs2).
Proof.
  destruct p.
  - unshelve esplit. now exact tt.
    now exact (mkCohPainting extraDepsCohs2).
  - unshelve esplit. now exact (mkCohPaintings p k.+1
      depsCohs2.(1)%depscohs2 (depsCohs2; extraDepsCohs2)%extradepscohs2).
    now exact (mkCohPainting extraDepsCohs2).
Defined.

Class νSetData p := {
  frames: mkFrameTypes p 0;
  paintings: mkPaintingTypes p 0 frames;
  restrFrames: mkRestrFrameTypes paintings;
  restrPaintings E: mkRestrPaintingTypes (TopRestrDep E);
  cohFrames E: mkCohFrameTypes (restrPaintings E);
  cohPaintings E E': mkCohPaintingTypes
    (depsCohs := toDepsCohs (deps := toDepsRestr restrFrames) (cohFrames E))
    (TopCohDep E');
}.

Section νSetData.
Variable p: nat.
Variable C: νSetData p.
Variable E: mkFrame (toDepsRestr C.(restrFrames)) -> HSet.

#[local]
Instance mkνSetData: νSetData p.+1 :=
{|
  frames := mkFrames _;
  paintings := mkPaintings _;
  restrFrames := mkRestrFrames;
  restrPaintings E' := mkRestrPaintings (TopCohDep E');
  cohFrames E' := mkCohFrames (C.(cohPaintings) E E');
  cohPaintings E' E'' :=
    mkCohPaintings (TopCoh2Dep (depsCohs2 := toDepsCohs2 (C.(cohPaintings) E E')) E'');
|}.
End νSetData.

Class νSet p := {
  prefix: Type;
  data: prefix -> νSetData p;
}.

(***************************************************)
(** The construction of [νSet n+1] from [νSet n] *)

(** Extending the initial prefix *)
Definition mkPrefix p {C: νSet p}: Type :=
  { D: C.(prefix) &T mkFrame (toDepsRestr (C.(data) D).(restrFrames)) -> HSet }.

#[local]
Instance mkνSet0: νSet 0.
  unshelve esplit.
  - now exact hunit.
  - unshelve esplit; try now trivial.
Defined.

#[local]
Instance mkνSet {p} (C: νSet p): νSet p.+1 :=
{|
  prefix := mkPrefix p;
  data := fun D: mkPrefix p => mkνSetData p (C.(data) D.1) D.2;
|}.

(** An [νSet] truncated up to dimension [n] *)
Fixpoint νSetAt n: νSet n :=
  match n with
  | O => mkνSet0
  | n.+1 => mkνSet (νSetAt n)
  end.

CoInductive νSetFrom n (X: (νSetAt n).(prefix)): Type := cons {
  this: mkFrame (toDepsRestr ((νSetAt n).(data) X).(restrFrames)) -> HSet;
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
