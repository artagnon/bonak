Set Warnings "-notation-overridden".
From Bonak Require Import SigT RewLemmas HSet Notation LeSProp.
From Bonak Require Import νGpd.HGpd νGpd.Layer νGpd.Lemmas.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module νGpd (A: LayerGpdSig).
Import A.
Module Export LT := LayerGpdTheory A.

(** The type of lists {frame(n,0);...;frame(n,p-1)} for arbitrary k := n-p
    (the non-mandatory dependency in k is useful for type inference) *)

Fixpoint mkFrameTypes p k: Type :=
  match p with
  | 0 => unit
  | S p => { frames: mkFrameTypes p k.+1 &T HGpd }
  end.

(** The type of lists {painting(n,0);...;painting(n,p-1)} for n := k+p *)

Fixpoint mkPaintingTypes p k: mkFrameTypes p k -> Type :=
  match p with
  | 0 => fun _ => unit
  | S p => fun frames =>
    { paintings: mkPaintingTypes p k.+1 frames.1 &T frames.2 -> HGpd }
  end.

(** A helper type so as to mutually build the types of restrFrames and
    the body of frames using a single fixpoint *)

Class RestrFrameTypeBlock p k := {
  RestrFrameTypesDef: Type;
  FrameDef: RestrFrameTypesDef -> mkFrameTypes p.+1 k;
}.

(**
For n and p<=n be given, and assuming {frame(n,0);...;frame(n,p)} and
{painting(n,0);...;painting(n,p)}, we build the list of pairs:
- of the types RestrFrameTypes(n,p) of the list
  {restrFrame(n,0);...;restrFrame(n,p-1)}
  (represented as an inhabitant of a sigma-type
   {R:RestrFrameTypes(n,0) & ... & RestrFrameTypes(n,p-1)})
- and of the list {frame(n+1,0);...;frame(n+1,p)} in function of effective
  restrFrames of type RestrFrameTypes(n,p)

That is, we build:
- p = 0 : { RestrFrameTypes(n,0..0-1) := unit ;
                  (which denotes the empty list of restrFrameTypes)
            Frames(n+1,0..0)(restrFrames^n_{0..0-1}) := {unit}
                  (representing lists by Sigma-types) }
- p = 1 : { RestrFrameTypes(n,0..0) = {_:unit & restrFrameType(n,0)} ;
                  (thus denoting the singleton list {restrFrameType(n,0})
            Frames(n+1,0..1)(restrFrames(n,0..0) :=
                  {unit;{d:Frame(n,0)&Painting(n,0)(restrFrame(n,0)(d)}} }
- ...
- p     : { RestrFrameTypes(n,0..p-1) =
              {RestrFrameType(n,0) & ... & RestrFrameType(n,p-1)} ;
            Frames(n+1,0..p)(restrFrames(n,0..p-1)) :=
              {frame(n+1,0);...;frame(n+1,p)} }

  In practise, it is convenient to work with the difference k := n-p
  rather than n itself. So, below, k is the difference.
*)

Generalizable Variables p k frames.

Definition mkRestrFrameType
  `(prevFrames: mkFrameTypes p.+1 k.+1)
   (frames: mkFrameTypes p.+1 k) :=
  forall q (Hq: q <= k) (ε: arity), prevFrames.2 -> frames.2.

Definition mkRestrFrameTypesStep `(frames: mkFrameTypes p.+1 k)
  (prev: RestrFrameTypeBlock p k.+1) :=
  { R: prev.(RestrFrameTypesDef) &T mkRestrFrameType (prev.(FrameDef) R) frames }.

Definition mkLayer `{frames: mkFrameTypes p.+1 k}
  {prevFrames: mkFrameTypes p.+1 k.+1}
  (restrFrame: mkRestrFrameType prevFrames frames)
  {painting: frames.2 -> HGpd}
  (d: prevFrames.2) :=
  Layer (fun ε => painting (restrFrame 0 leR_O ε d)).

Fixpoint mkRestrFrameTypesAndFrames {p k}:
  forall `(paintings: mkPaintingTypes p k frames), RestrFrameTypeBlock p k :=
  match p with
  | 0 => fun frames paintings =>
    {|
      RestrFrameTypesDef := unit;
      FrameDef _ := (tt; gunit): mkFrameTypes 1 k
    |}
  | p.+1 => fun frames paintings =>
    let prev :=
      mkRestrFrameTypesAndFrames paintings.1 in
    let frames' := prev.(FrameDef) in
    {|
      RestrFrameTypesDef := mkRestrFrameTypesStep frames prev;
      FrameDef R :=
        (frames' R.1; { d: (frames' R.1).2 &
          mkLayer R.2 (painting := paintings.2) d }): mkFrameTypes p.+2 k
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

Definition mkFrame `(deps: DepsRestr p k): HGpd := (mkFrames deps).2.

Inductive DepsRestrExtension p: forall k, DepsRestr p k -> Type :=
| TopRestrDep {deps} (E: mkFrame deps -> HGpd): DepsRestrExtension p 0 deps
| AddRestrDep {k} deps:
  DepsRestrExtension p.+1 k deps -> DepsRestrExtension p k.+1 deps.(1).

Arguments TopRestrDep {p deps}.
Arguments AddRestrDep {p k} deps.

Declare Scope extra_depsrestr_scope.
Delimit Scope extra_depsrestr_scope with extradepsrestr.
Bind Scope extra_depsrestr_scope with DepsRestrExtension.
Notation "( x ; y )" := (AddRestrDep x y)
  (at level 0, format "( x ; y )"): extra_depsrestr_scope.

(* Example: if p := 0, extraDeps := ({},E) mkPainting:= {E} *)

Generalizable Variables deps.

Fixpoint mkPainting `(extraDeps: DepsRestrExtension p k deps):
  mkFrame deps -> HGpd :=
  match extraDeps with
  | TopRestrDep E => fun d => E d
  | AddRestrDep deps extraDeps => fun (d: mkFrame deps.(1)) =>
      {l: mkLayer deps.(_restrFrames).2 d & mkPainting extraDeps (d; l)}
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

Definition mkCohFrameType `{extraDeps: DepsRestrExtension p.+1 k deps}
  (prevRestrFrames: mkRestrFrameTypes (mkPaintings (deps; extraDeps))): Type :=
  forall q (Hq: q <= k) r (Hr: r <= q) (ε ω: arity)
    (d: mkFrame (toDepsRestr prevRestrFrames).(1)),
  deps.(_restrFrames).2 q Hq ε (prevRestrFrames.2 r (Hr ↕ (↑ Hq)) ω d) =
  deps.(_restrFrames).2 r (Hr ↕ Hq) ω (prevRestrFrames.2 q.+1 (⇑ Hq) ε d).

Definition mkCohFrameTypesStep `{extraDeps: DepsRestrExtension p.+1 k deps}
  (prev: CohFrameTypeBlock (extraDeps := (deps; extraDeps))): Type :=
  { Q: prev.(CohFrameTypesDef) &T mkCohFrameType (prev.(RestrFramesDef) Q) }.

Definition mkRestrLayer `{extraDeps: DepsRestrExtension p.+1 k deps}
  {prevRestrFrames: mkRestrFrameTypes (mkPaintings (deps;extraDeps))}
  (restrPainting: mkRestrPaintingType extraDeps)
  (cohFrame: mkCohFrameType prevRestrFrames)
  q (Hq: q <= k) (ε: arity)
  (d: mkFrame (toDepsRestr prevRestrFrames).(1))
  (l: mkLayer prevRestrFrames.2 d):
  mkLayer deps.(_restrFrames).2 (prevRestrFrames.2 q.+1 (⇑ Hq) ε d) :=
  lmap (fun ω c =>
    rew [deps.(_paintings).2] cohFrame q Hq 0 leR_O ε ω d in
    restrPainting q Hq ε _ c) l.

(** Under previous assumptions, and, additionally:
    - {restrPainting(n,0);...;restrPainting(n,p-1)}
    we mutually build the pair of:
    - the list of types for {cohFrame(n,0);...;cohFrame(n,p-1)}
    - definitions of {restrFrame(n+1,0);...;restrFrame(n+1,p)} *)

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
      let restrFrame q (Hq: q <= k) (ε: arity)
        (d: mkFrame (toDepsRestr (restrFrames Q.1))) :=
          ((restrFrames Q.1).2 q.+1 (⇑ Hq) ε d.1;
           mkRestrLayer restrPaintings.2 Q.2 q _ ε d.1 d.2)
      in (restrFrames Q.1; restrFrame)
    |}
  end.

(* Example: if p := 0, extraDeps := ({},E)
   mkCohFrameTypes := {} *)

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
     - {frame(n,0);...;frame(n,p-1)}
     - {painting(n,0);...;painting(n,p-1)}
     - {restrFrame(n,0);...;restrFrame(n,p-1)} for p<=n+1
     (forming a "deps"), and
     - {frame(n,p);...;frame(n,n)}
     - {painting(n,p);...;painting(n,n)}
     - {restrFrame(n,p);...;restrFrame(n,n)}
     - E:frame(n+1,n+1) -> HGpd
     (forming an "extraDeps")
     we form:
     - {frame(n+1,0);...;frame(n+1,p)} (built by mkFrames)
     - {painting(n+1,0);...;painting(p+n,p)} (built by mkPaintings)
     - {restrFrame(n+1,0);...;restrFrame(n+1,p)} (built by mkRestrFrames)

   Example: if p := 0, extraDeps := ({},E), restrPaintings := {}, cohs := {}
   then mkDepsRestr := {frames'':={unit};
                        paintings'':={E};
                        restrFrames':={λq().()}}
   (where restrFrames' is presented as a dependent pair, i.e. ((),λq().()) *)

Definition mkDepsRestr `{depsCohs: DepsCohs p k} :=
  toDepsRestr mkRestrFrames.

(** Deducing restrFrame(n+1,p) *)

(** Note that we use mkRestrFrames(n+1,p) both to build frame(n+2,p) and
    restrFrame(n+1,p) : frame(n+2,p) -> frame(n+1,p), according to the
    circularity between Frames and RestrFrameTypes.
    But now, thanks to restrPaintings and cohFrames, we have an effective
    definition of RestrFrame(n+1,p) and the circular dependency of
    frame(n+2,p) with an inhabitant RestrFrame(n+1,p) of RestrFrameType(n+1,p)
    is gone.
 *)

Definition mkRestrFrame `{depsCohs: DepsCohs p k}:
  forall q (Hq: q <= k) (ε: arity),
  mkFrame mkDepsRestr.(1) -> mkFrame depsCohs.(_deps) :=
  mkRestrFrames.2.

Inductive DepsCohsExtension p: forall k (depsCohs: DepsCohs p k), Type :=
| TopCohDep `{depsCohs: DepsCohs p 0}
  (E: mkFrame mkDepsRestr -> HGpd):
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
  DepsRestrExtension p.+1 k mkDepsRestr.
Proof.
  destruct extraDepsCohs.
  - now constructor.
  - apply (AddRestrDep mkDepsRestr
    (mkExtraDeps p.+1 k depsCohs extraDepsCohs)).
Defined.

Fixpoint mkRestrPainting `(extraDepsCohs: DepsCohsExtension p k depsCohs)
  q {struct q}:
  forall (Hq: q <= k) (ε: arity) (d: mkFrame mkDepsRestr.(1)),
    (mkPaintings (mkDepsRestr; mkExtraDeps extraDepsCohs)).2 d ->
    mkDepsRestr.(_paintings).2 (mkDepsRestr.(_restrFrames).2 q Hq ε d).
Proof.
  destruct q as [|q]; intros Hq ε d [l c].
  - exact (nth l ε).
  - destruct extraDepsCohs as [|k0 depsCohs0 extraDepsCohs0].
    + now destruct (leR_O_contra Hq).
    + unshelve eapply existT.
      * exact (mkRestrLayer depsCohs0.(_restrPaintings).2 depsCohs0.(_cohs).2
          q (⇓ Hq) ε d l).
      * exact (mkRestrPainting _ _ _ extraDepsCohs0 q (⇓ Hq) ε (d; l) c).
Defined.

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

(** The groupoid-level replacement for the old [mkCoh2Frame] UIP proof:
    this is now explicit 2-dimensional frame coherence data. *)

Definition mkCoh2FrameType
  `(extraDepsCohs: DepsCohsExtension p.+1 k depsCohs)
  (prevCohFrames: mkCohFrameTypes
    (mkRestrPaintings (depsCohs; extraDepsCohs))): Type :=
  forall q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) (ε ω θ: arity)
    (d: mkFrame (mkDepsRestr (depsCohs := toDepsCohs prevCohFrames.1)).(1)),
  f_equal
    (fun x => depsCohs.(_deps).(_restrFrames).2 q _ ε x)
    (prevCohFrames.2 r (Hr ↕ ↑ Hq) s Hs ω θ d)
  • (depsCohs.(_cohs).2 q Hq s (Hs ↕ Hr) ε θ
      (mkRestrFrame r.+1 (⇑ (Hr ↕ ↑ Hq)) ω d)
  • f_equal
      (fun x => depsCohs.(_deps).(_restrFrames).2 s (Hs ↕ (Hr ↕ Hq)) θ x)
      (prevCohFrames.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) ε ω d)) =
  depsCohs.(_cohs).2 q Hq r Hr ε ω
    (mkRestrFrame s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) θ d)
  • (f_equal
      (fun x => depsCohs.(_deps).(_restrFrames).2 r _ ω x)
      (prevCohFrames.2 q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) ε θ d)
  • depsCohs.(_cohs).2 r (Hr ↕ Hq) s Hs ω θ
      (mkRestrFrame q.+2 (⇑ (⇑ Hq)) ε d)).

Definition mkCohPaintingType
  `(extraDepsCohs: DepsCohsExtension p.+1 k depsCohs) :=
  forall q (Hq: q <= k) r (Hr: r <= q) (ε ω: arity)
    (d: mkFrame mkDepsRestr.(1))
    (c: (mkPaintings (mkDepsRestr;
      mkExtraDeps (depsCohs; extraDepsCohs))).2 d),
  rew [depsCohs.(_deps).(_paintings).2] depsCohs.(_cohs).2 q Hq r Hr ε ω d in
  depsCohs.(_restrPaintings).2 q Hq ε _
    ((mkRestrPaintings (depsCohs; extraDepsCohs)).2 r _ ω d c) =
  depsCohs.(_restrPaintings).2 r (Hr ↕ Hq) ω _
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

Definition mkCohLayerType `{extraDepsCohs: DepsCohsExtension p.+1 k depsCohs}
  {prevCohFrames: mkCohFrameTypes
    (extraDeps := (mkDepsRestr; mkExtraDeps extraDepsCohs))
    (mkRestrPaintings extraDepsCohs).1}
  q (Hq: q <= k) r (Hr: r <= q) (ε ω: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := toDepsCohs prevCohFrames.1)).(1))
  (l: mkLayer mkRestrFrame d): Type :=
  rew [mkLayer _] prevCohFrames.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) ε ω d in
  mkRestrLayer depsCohs.(_restrPaintings).2 depsCohs.(_cohs).2 q Hq ε _
    (mkRestrLayer (mkRestrPaintings extraDepsCohs).1.2 prevCohFrames.2
      r (Hr ↕ ↑ Hq) ω d l) =
  mkRestrLayer depsCohs.(_restrPaintings).2 depsCohs.(_cohs).2 r (Hr ↕ Hq) ω _
    (mkRestrLayer (mkRestrPaintings extraDepsCohs).1.2 prevCohFrames.2
      q.+1 (⇑ Hq) ε d l).

Definition mkCohLayer `{extraDepsCohs: DepsCohsExtension p.+1 k depsCohs}
  {prevCohFrames: mkCohFrameTypes
    (extraDeps := (mkDepsRestr; mkExtraDeps extraDepsCohs))
    (mkRestrPaintings extraDepsCohs).1}
  (cohPainting: mkCohPaintingType extraDepsCohs)
  (coh2Frame: mkCoh2FrameType extraDepsCohs prevCohFrames)
  q (Hq: q <= k) r (Hr: r <= q) (ε ω: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := toDepsCohs prevCohFrames.1)).(1))
  (l: mkLayer mkRestrFrame d):
  mkCohLayerType q Hq r Hr ε ω d l.
Proof.
  unfold mkCohLayerType, mkRestrLayer.
  apply (lmap2_rew_eq
    (P := fun x => depsCohs.(_deps).(_paintings).2 x)
    (rf0 := fun a x => depsCohs.(_deps).(_restrFrames).2 0 leR_O a x));
    intro θ.
  eapply (rew_cohLayer33
    (P := fun x => depsCohs.(_deps).(_paintings).2 x)
    (rf0 := fun x => depsCohs.(_deps).(_restrFrames).2 0 leR_O θ x)
    (F := depsCohs.(_restrPaintings).2 q Hq ε)
    (G := depsCohs.(_restrPaintings).2 r (Hr ↕ Hq) ω)).
  - now exact (cohPainting q Hq r Hr ε ω
      (((mkCohFrameTypesAndRestrFrames (mkRestrPaintings extraDepsCohs).1.1)
        .(RestrFramesDef) prevCohFrames.1).2 0 leR_O θ d) (nth l θ)).
  - now apply (coh2Frame q Hq r Hr 0 leR_O ε ω θ d).
Defined.

Class Coh2FrameTypeBlock `{extraDepsCohs: DepsCohsExtension p k depsCohs} := {
  Coh2FrameTypesDef: Type;
  CohFramesDef: Coh2FrameTypesDef -> mkCohFrameTypes (mkRestrPaintings extraDepsCohs);
}.

Definition mkCoh2FrameTypesStep
  `{extraDepsCohs: DepsCohsExtension p.+1 k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs)
  (prev: Coh2FrameTypeBlock
    (extraDepsCohs := (depsCohs; extraDepsCohs)%extradepscohs)): Type :=
  { R: prev.(Coh2FrameTypesDef) &T
    mkCoh2FrameType extraDepsCohs (prev.(CohFramesDef) R) }.

Fixpoint mkCoh2FrameTypesAndCohFrames {p k}:
  forall `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs),
  Coh2FrameTypeBlock (extraDepsCohs := extraDepsCohs).
Proof.
  destruct p.
  - intros depsCohs extraDepsCohs cohPaintings.
    unshelve econstructor.
    + now exact unit.
    + intros _. unshelve esplit. now exact tt. now intros.
  - intros depsCohs extraDepsCohs cohPaintings.
    set (prev := mkCoh2FrameTypesAndCohFrames p k.+1
      depsCohs.(1)%depscohs
      (depsCohs; extraDepsCohs)%extradepscohs cohPaintings.1).
    unshelve econstructor.
    + now exact (mkCoh2FrameTypesStep cohPaintings prev).
    + intros Q.
      set (h := prev.(CohFramesDef) Q.1).
      unshelve esplit. now exact h.
      intros q Hq r Hr ε ω d.
      unshelve eapply eq_existT_curried.
      * now exact (h.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) ε ω d.1).
      * now exact (mkCohLayer cohPaintings.2 Q.2 q Hq r Hr ε ω d.1 d.2).
Defined.

Definition mkCoh2FrameTypes `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs) :=
  (mkCoh2FrameTypesAndCohFrames cohPaintings).(Coh2FrameTypesDef).

Definition mkCohFrames `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs)
  (coh2Frames: mkCoh2FrameTypes cohPaintings):
  mkCohFrameTypes (mkRestrPaintings extraDepsCohs) :=
  (mkCoh2FrameTypesAndCohFrames cohPaintings).(CohFramesDef) coh2Frames.

Definition mkCohFrame `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  (cohPaintings: mkCohPaintingTypes extraDepsCohs)
  (coh2Frames: mkCoh2FrameTypes cohPaintings):
  mkCohFrameType (mkRestrFrames (depsCohs :=
    toDepsCohs (mkCohFrames cohPaintings coh2Frames).1)) :=
  (mkCohFrames cohPaintings coh2Frames).2.

Class DepsCohs2 p k := {
  _depsCohs: DepsCohs p k;
  _extraDepsCohs: DepsCohsExtension p k _depsCohs;
  _cohPaintings: mkCohPaintingTypes _extraDepsCohs;
  _coh2Frames: mkCoh2FrameTypes _cohPaintings;
}.

#[local]
Instance toDepsCohs2 `{extraDepsCohs: DepsCohsExtension p k depsCohs}
  {cohPaintings: mkCohPaintingTypes extraDepsCohs}
  (coh2Frames: mkCoh2FrameTypes cohPaintings): DepsCohs2 p k :=
  {| _coh2Frames := coh2Frames |}.

#[local]
Instance proj1DepsCohs2 `(depsCohs2: DepsCohs2 p.+1 k): DepsCohs2 p k.+1 :=
{|
  _depsCohs := depsCohs2.(_depsCohs).(1);
  _extraDepsCohs := (depsCohs2.(_depsCohs); depsCohs2.(_extraDepsCohs));
  _cohPaintings := depsCohs2.(_cohPaintings).1;
  _coh2Frames := depsCohs2.(_coh2Frames).1;
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
  _cohs := mkCohFrames depsCohs2.(_cohPaintings) depsCohs2.(_coh2Frames);
|}.

Inductive DepsCohs2Extension p: forall k (depsCohs2: DepsCohs2 p k), Type :=
| TopCoh2Dep `{depsCohs2: DepsCohs2 p 0}
  (E: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs depsCohs2)) -> HGpd):
  DepsCohs2Extension p 0 depsCohs2
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

Definition mkCohPainting `{depsCohs2: DepsCohs2 p k}
  (extraDepsCohs2: DepsCohs2Extension p k depsCohs2):
  mkCohPaintingType (mkExtraCohs extraDepsCohs2).
Proof.
  intros q Hq r.
  generalize dependent q.
  generalize dependent k.
  generalize dependent p.
  induction r as [|r mkCohPainting].
  - intros p k depsCohs2 extraDepsCohs2 q Hq Hr ε ω d c.
    now exact (eq_sym (nth_lmap _ c.1 ω)).
  - intros p k depsCohs2 extraDepsCohs2 q Hq Hr ε ω d c.
    destruct q; [now contradict Hq |].
    destruct extraDepsCohs2; [now contradict Hq |].
    destruct c as [l c].
    unshelve eapply (eq_existT_curried_dep
      (Q := mkPainting depsCohs2.(_depsCohs).(_extraDeps))).
    + now exact (mkCohLayer depsCohs2.(_cohPaintings).2 depsCohs2.(_coh2Frames).2
        q (⇓ Hq) r (⇓ Hr) ε ω d l).
    + now exact (mkCohPainting p.+1 k depsCohs2 extraDepsCohs2
        q (⇓ Hq) (⇓ Hr) ε ω (d; l) c).
Defined.

Fixpoint mkCohPaintingsPrefix `{depsCohs2: DepsCohs2 p k}
  (extraDepsCohs2: DepsCohs2Extension p k depsCohs2) {struct p}:
  @mkCohPaintingTypes p k.+1 (mkDepsCohs depsCohs2).(1)
    (mkDepsCohs depsCohs2; mkExtraCohs extraDepsCohs2)%extradepscohs.
Proof.
  destruct p.
  - now exact tt.
  - unshelve esplit.
    + now exact (mkCohPaintingsPrefix p k.+1 depsCohs2.(1)%depscohs2
        (depsCohs2; extraDepsCohs2)%extradepscohs2).
    + now exact (mkCohPainting (depsCohs2; extraDepsCohs2)%extradepscohs2).
Defined.

Definition mkCohPaintings `{depsCohs2: DepsCohs2 p k}
  (extraDepsCohs2: DepsCohs2Extension p k depsCohs2):
  mkCohPaintingTypes (mkExtraCohs extraDepsCohs2) :=
  (mkCohPaintingsPrefix extraDepsCohs2; mkCohPainting extraDepsCohs2).

Definition mkCoh2PaintingSourcePainting {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  (extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2)
  (d: mkFrame ((mkDepsRestr (depsCohs := (mkDepsCohs depsCohs2).(1).(1)))).(1)): HGpd :=
  (mkPaintings ((mkDepsRestr (depsCohs := mkDepsCohs depsCohs2)).(1).(1);
    mkExtraDeps ((mkDepsCohs depsCohs2).(1); (mkDepsCohs depsCohs2;
      mkExtraCohs extraDepsCohs2)))).2 d.

Definition mkCoh2PaintingFrameEndpointType {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) (ε ω θ: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := (mkDepsCohs depsCohs2).(1).(1))).(1)): Type :=
  depsCohs2.(_depsCohs).(_deps).(_restrFrames).2 q Hq ε
    (mkRestrFrame (depsCohs := depsCohs2.(_depsCohs).(1)) r (Hr ↕ ↑ Hq) ω
      (mkRestrFrame s (Hs ↕ ↑ (Hr ↕ ↑ Hq)) θ d)) =
  depsCohs2.(_depsCohs).(_deps).(_restrFrames).2 s (Hs ↕ (Hr ↕ Hq)) θ
    (mkRestrFrame (depsCohs := depsCohs2.(_depsCohs).(1)) r.+1 (⇑ Hr ↕ ⇑ Hq) ω
      (mkRestrFrame q.+2 (⇑ (⇑ Hq)) ε d)).

Definition mkCoh2PaintingEndpointType {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  (extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) (ε ω θ: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := (mkDepsCohs depsCohs2).(1).(1))).(1))
  (c: mkCoh2PaintingSourcePainting depsCohs2 extraDepsCohs2 d)
  (coh2FrameEndpoint: mkCoh2PaintingFrameEndpointType
    depsCohs2 q Hq r Hr s Hs ε ω θ d): Type :=
  let restrPainting1 := mkRestrPainting
    (depsCohs2.(_depsCohs); depsCohs2.(_extraDepsCohs)) in
  let restrPainting2 := mkRestrPainting ((mkDepsCohs depsCohs2).(1);
    (mkDepsCohs depsCohs2; mkExtraCohs extraDepsCohs2)) in
  rew [depsCohs2.(_depsCohs).(_deps).(_paintings).2] coh2FrameEndpoint in
  depsCohs2.(_depsCohs).(_restrPaintings).2 q Hq ε _
    (restrPainting1 r (Hr ↕ ↑ Hq) ω _
      (restrPainting2 s (Hs ↕ ↑ (Hr ↕ ↑ Hq)) θ d c)) =
  depsCohs2.(_depsCohs).(_restrPaintings).2 s (Hs ↕ (Hr ↕ Hq)) θ _
    (restrPainting1 r.+1 (⇑ Hr ↕ ⇑ Hq) ω _
      (restrPainting2 q.+2 (⇑ (⇑ Hq)) ε d c)).

(** The instance body is a named definition so that goals stay one line:
    tactics like [destruct] re-typecheck their motive, which is
    prohibitive over the unfolded body (observed: ~28s for
    [destruct c] in [mkCoh2Painting] on the raw body, negligible once
    folded). *)
Definition mkCoh2PaintingInstanceType {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  (extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) (ε ω θ: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := (mkDepsCohs depsCohs2).(1).(1))).(1))
  (c: mkCoh2PaintingSourcePainting depsCohs2 extraDepsCohs2 d): Type :=
  let depsCohs := depsCohs2.(_depsCohs) in
  let restrPainting2 := mkRestrPainting ((mkDepsCohs depsCohs2).(1);
    (mkDepsCohs depsCohs2; mkExtraCohs extraDepsCohs2)) in
  rew [mkCoh2PaintingEndpointType depsCohs2 extraDepsCohs2
        q Hq r Hr s Hs ε ω θ d c]
    depsCohs2.(_coh2Frames).2 q Hq r Hr s Hs ε ω θ d in
  (sigT_map_eq (Q := fun x => GDom (depsCohs.(_deps).(_paintings).2 x))
    (depsCohs.(_restrPaintings).2 q Hq ε)
    (mkCohPainting (depsCohs2; extraDepsCohs2) r (Hr ↕ ↑ Hq) s Hs ω θ d c)
  ⊙ (depsCohs2.(_cohPaintings).2 q Hq s (Hs ↕ Hr) ε θ
      (mkRestrFrame r.+1 (⇑ (Hr ↕ ↑ Hq)) ω d)
      (restrPainting2 r.+1 (⇑ (Hr ↕ ↑ Hq)) ω d c)
  ⊙[fun x => GDom (depsCohs.(_deps).(_paintings).2 x)]
    sigT_map_eq (Q := fun x => GDom (depsCohs.(_deps).(_paintings).2 x))
      (depsCohs.(_restrPaintings).2 s (Hs ↕ (Hr ↕ Hq)) θ)
      (mkCohPainting (depsCohs2; extraDepsCohs2)
        q.+1 (⇑ Hq) r.+1 (⇑ Hr) ε ω d c))) =
  depsCohs2.(_cohPaintings).2 q Hq r Hr ε ω
    (mkRestrFrame s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) θ d)
    (restrPainting2 s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) θ d c)
  ⊙[fun x => GDom (depsCohs.(_deps).(_paintings).2 x)]
    (sigT_map_eq (Q := fun x => GDom (depsCohs.(_deps).(_paintings).2 x))
      (depsCohs.(_restrPaintings).2 r (Hr ↕ Hq) ω)
      (mkCohPainting (depsCohs2; extraDepsCohs2)
        q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) ε θ d c)
  ⊙ depsCohs2.(_cohPaintings).2 r (Hr ↕ Hq) s Hs ω θ
      (mkRestrFrame q.+2 (⇑ (⇑ Hq)) ε d)
      (restrPainting2 q.+2 (⇑ (⇑ Hq)) ε d c)).

Definition mkCoh2PaintingType {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  (extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2): Type :=
  forall
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) (ε ω θ: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := (mkDepsCohs depsCohs2).(1).(1))).(1))
  (c: mkCoh2PaintingSourcePainting depsCohs2 extraDepsCohs2 d),
  mkCoh2PaintingInstanceType depsCohs2 extraDepsCohs2
    q Hq r Hr s Hs ε ω θ d c.

Fixpoint mkCoh2PaintingTypes {p}:
  forall `{extraDepsCohs2: DepsCohs2Extension p k depsCohs2}, Type :=
  match p with
  | 0 => fun _ _ _ => unit
  | S p =>
    fun k depsCohs2 extraDepsCohs2 =>
    { R: @mkCoh2PaintingTypes p k.+1 depsCohs2.(1)%depscohs2
        (depsCohs2; extraDepsCohs2)%extradepscohs2 &T
         mkCoh2PaintingType depsCohs2 extraDepsCohs2 }
  end.

Arguments mkCoh2PaintingTypes {p k depsCohs2} extraDepsCohs2.

Definition mkCoh2LayerFrameEndpointType {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  (extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2)
  (coh2Frames: mkCoh2FrameTypes (mkCohPaintings (depsCohs2; extraDepsCohs2)))
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) (ε ω θ: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := toDepsCohs (mkCohFrames
    (mkCohPaintings (depsCohs2; extraDepsCohs2)).1 coh2Frames.1).1)).(1)): Type :=
  mkRestrFrames.2 q.+1 (⇑ Hq) ε
    (mkRestrFrames.2 r.+1 (⇑ (Hr ↕ ↑ Hq)) ω
      (mkRestrFrames.2 s.+1 (⇑ (Hs ↕ ↑ (Hr ↕ ↑ Hq))) θ d)) =
  (mkRestrFrames.2 s.+1 (⇑ (Hs ↕ (Hr ↕ Hq))) θ
    (mkRestrFrames.2 r.+2 (⇑ (⇑ Hr ↕ ⇑ Hq)) ω
      (mkRestrFrames.2 q.+3 (⇑ (⇑ (⇑ Hq))) ε d))).

Definition mkCoh2LayerEndpointType {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  (extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2)
  (prevCoh2Frames: mkCoh2FrameTypes (mkCohPaintings (depsCohs2; extraDepsCohs2)))
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) (ε ω θ: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := toDepsCohs (mkCohFrames
    (mkCohPaintings (depsCohs2; extraDepsCohs2)).1 prevCoh2Frames.1).1)).(1))
  (l: mkLayer (mkDepsRestr (depsCohs := toDepsCohs (mkCohFrames
    (mkCohPaintings (depsCohs2; extraDepsCohs2)).1 prevCoh2Frames.1).1)).(_restrFrames).2 d)
  (coh2FrameEndpoint: mkCoh2LayerFrameEndpointType depsCohs2
    extraDepsCohs2 prevCoh2Frames q Hq r Hr s Hs ε ω θ d): Type :=
  let depsCohs := depsCohs2.(_depsCohs) in
  let cohFrame1 := mkCohFrame depsCohs2.(_cohPaintings).1 depsCohs2.(_coh2Frames).1 in
  let restrPainting1 := mkRestrPainting (depsCohs; depsCohs2.(_extraDepsCohs)) in
  let cohFrame2 := mkCohFrame (mkCohPaintings (depsCohs2; extraDepsCohs2)).1 prevCoh2Frames.1 in
  let restrPainting2 := mkRestrPainting ((mkDepsCohs depsCohs2).(1);
    (mkDepsCohs depsCohs2; mkExtraCohs extraDepsCohs2)) in
  rew [mkLayer depsCohs.(_deps).(_restrFrames).2] coh2FrameEndpoint in
  mkRestrLayer depsCohs.(_restrPaintings).2 depsCohs.(_cohs).2 q Hq ε
    (mkRestrFrame r.+1 (⇑ (Hr ↕ ↑ Hq)) ω
      (mkRestrFrame s.+1 (⇑ (Hs ↕ ↑ (Hr ↕ ↑ Hq))) θ d))
    (mkRestrLayer restrPainting1 cohFrame1 r (Hr ↕ ↑ Hq) ω
      (mkRestrFrame s.+1 (⇑ (Hs ↕ ↑ (Hr ↕ ↑ Hq))) θ d)
      (mkRestrLayer restrPainting2 cohFrame2 s (Hs ↕ ↑ (Hr ↕ ↑ Hq)) θ d l)) =
  mkRestrLayer depsCohs.(_restrPaintings).2 depsCohs.(_cohs).2
    s (Hs ↕ (Hr ↕ Hq)) θ
    (mkRestrFrame r.+2 (⇑ (⇑ Hr ↕ ⇑ Hq)) ω
      (mkRestrFrame q.+3 (⇑ (⇑ (⇑ Hq))) ε d))
    (mkRestrLayer restrPainting1 cohFrame1 r.+1 (⇑ Hr ↕ ⇑ Hq) ω
      (mkRestrFrame q.+3 (⇑ (⇑ (⇑ Hq))) ε d)
      (mkRestrLayer restrPainting2 cohFrame2 q.+2 (⇑ (⇑ Hq)) ε d l)).

Definition mkCoh2LayerType {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  (extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2)
  (prevCoh2Frames: mkCoh2FrameTypes (mkCohPaintings (depsCohs2;extraDepsCohs2)))
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) (ε ω θ: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := toDepsCohs (mkCohFrames
    (mkCohPaintings (depsCohs2; extraDepsCohs2)).1 prevCoh2Frames.1).1)).(1))
  (l: mkLayer (mkDepsRestr (depsCohs := toDepsCohs (mkCohFrames (mkCohPaintings
    (depsCohs2; extraDepsCohs2)).1 prevCoh2Frames.1).1)).(_restrFrames).2 d): Type :=
  let depsCohs := depsCohs2.(_depsCohs) in
  let depsCohs' := toDepsCohs (mkCohFrames
    (mkCohPaintings (depsCohs2; extraDepsCohs2)).1 prevCoh2Frames.1) in
  rew [mkCoh2LayerEndpointType depsCohs2 extraDepsCohs2 prevCoh2Frames
        q Hq r Hr s Hs ε ω θ d l]
    prevCoh2Frames.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) s.+1 (⇑ Hs) ε ω θ d in
  (sigT_map_eq (Q := fun x => GDom (mkLayer depsCohs.(_deps).(_restrFrames).2 x))
    (mkRestrLayer depsCohs2.(_depsCohs).(_restrPaintings).2
      depsCohs2.(_depsCohs).(_cohs).2 q Hq ε)
    (mkCohLayer (mkCohPaintings extraDepsCohs2).1.2
      prevCoh2Frames.2 r (Hr ↕ ↑ Hq) s Hs ω θ d l)
  ⊙ (mkCohLayer depsCohs2.(_cohPaintings).2
    depsCohs2.(_coh2Frames).2 q Hq s (Hs ↕ Hr) ε θ
      (mkRestrFrame (depsCohs := depsCohs') r.+1 (⇑ (Hr ↕ ↑ Hq)) ω (d; l)).1
      (mkRestrFrame (depsCohs := depsCohs') r.+1 (⇑ (Hr ↕ ↑ Hq)) ω (d; l)).2
  ⊙[fun x => GDom (mkLayer depsCohs.(_deps).(_restrFrames).2 x)]
    sigT_map_eq (Q := fun x => GDom (mkLayer depsCohs.(_deps).(_restrFrames).2 x))
      (mkRestrLayer depsCohs2.(_depsCohs).(_restrPaintings).2
        depsCohs2.(_depsCohs).(_cohs).2 s (Hs ↕ (Hr ↕ Hq)) θ)
      (mkCohLayer (mkCohPaintings extraDepsCohs2).1.2 prevCoh2Frames.2
        q.+1 (⇑ Hq) r.+1 (⇑ Hr) ε ω d l))) =
  mkCohLayer depsCohs2.(_cohPaintings).2
    depsCohs2.(_coh2Frames).2 q Hq r Hr ε ω
    (mkRestrFrame (depsCohs := depsCohs') s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) θ (d; l)).1
    (mkRestrFrame (depsCohs := depsCohs') s (↑ (↑ (Hs ↕ (Hr ↕ Hq)))) θ (d; l)).2
  ⊙[fun x => GDom (mkLayer depsCohs.(_deps).(_restrFrames).2 x)]
    (sigT_map_eq (Q := fun x => GDom (mkLayer depsCohs.(_deps).(_restrFrames).2 x))
      (mkRestrLayer depsCohs2.(_depsCohs).(_restrPaintings).2
        depsCohs2.(_depsCohs).(_cohs).2 r (Hr ↕ Hq) ω)
      (mkCohLayer (mkCohPaintings extraDepsCohs2).1.2
        prevCoh2Frames.2 q.+1 (⇑ Hq) s (↑ (Hs ↕ Hr)) ε θ d l)
  ⊙ mkCohLayer depsCohs2.(_cohPaintings).2
      depsCohs2.(_coh2Frames).2 r (Hr ↕ Hq) s Hs ω θ
      (mkRestrFrame (depsCohs := depsCohs') q.+2 (⇑ (⇑ Hq)) ε (d; l)).1
      (mkRestrFrame (depsCohs := depsCohs') q.+2 (⇑ (⇑ Hq)) ε (d; l)).2).

Definition mkCoh2Layer {p k}
  (depsCohs2: DepsCohs2 p.+1 k)
  (extraDepsCohs2: DepsCohs2Extension p.+1 k depsCohs2)
  (prevCoh2Frames: mkCoh2FrameTypes (mkCohPaintings (depsCohs2;extraDepsCohs2)))
  (coh2Painting: mkCoh2PaintingType depsCohs2 extraDepsCohs2)
  (* coh3Frame: mkCoh3FrameType ... - not needed as for HGpd is given by GUIP *)
  q (Hq: q <= k) r (Hr: r <= q) s (Hs: s <= r) (ε ω θ: arity)
  (d: mkFrame (mkDepsRestr (depsCohs := toDepsCohs (mkCohFrames
    (mkCohPaintings (depsCohs2; extraDepsCohs2)).1 prevCoh2Frames.1).1)).(1))
  (l: mkLayer (mkDepsRestr (depsCohs := toDepsCohs (mkCohFrames
    (mkCohPaintings (depsCohs2; extraDepsCohs2)).1 prevCoh2Frames.1).1)).(_restrFrames).2 d):
  mkCoh2LayerType depsCohs2 extraDepsCohs2 prevCoh2Frames
    q Hq r Hr s Hs ε ω θ d l.
Proof.
  unfold mkCoh2LayerType, mkCoh2LayerEndpointType, mkCoh2LayerFrameEndpointType.
  cbv beta zeta.
  eapply (lmap2_hex_rew_eq
    (P := fun x => depsCohs2.(_depsCohs).(_deps).(_paintings).2 x)
    (rf0 := fun a x =>
      depsCohs2.(_depsCohs).(_deps).(_restrFrames).2 0 leR_O a x)
    (S := fun x => (mkDepsCohs depsCohs2).(1).(_deps).(_paintings).2 x)
    (uf0 := fun a x =>
      (mkDepsCohs depsCohs2).(1).(_deps).(_restrFrames).2 0 leR_O a x)
    (NA := fun dd ω0 c =>
      rew [fun x => depsCohs2.(_depsCohs).(_deps).(_paintings).2 x]
        depsCohs2.(_depsCohs).(_cohs).2 q Hq 0 leR_O ε ω0 dd in
      depsCohs2.(_depsCohs).(_restrPaintings).2 q Hq ε _ c)
    (NB := fun dd ω0 c =>
      rew [fun x => depsCohs2.(_depsCohs).(_deps).(_paintings).2 x]
        depsCohs2.(_depsCohs).(_cohs).2 s (Hs ↕ (Hr ↕ Hq)) 0 leR_O θ ω0 dd in
      depsCohs2.(_depsCohs).(_restrPaintings).2 s (Hs ↕ (Hr ↕ Hq)) θ _ c)
    (NC := fun dd ω0 c =>
      rew [fun x => depsCohs2.(_depsCohs).(_deps).(_paintings).2 x]
        depsCohs2.(_depsCohs).(_cohs).2 r (Hr ↕ Hq) 0 leR_O ω ω0 dd in
      depsCohs2.(_depsCohs).(_restrPaintings).2 r (Hr ↕ Hq) ω _ c)).
  intro ζ; unfold lmap2_hex_pointwise.
  eapply (rew_coh2Layer
    (S0 := fun x => depsCohs2.(_depsCohs).(_deps).(_paintings).2 x)
    (rf0 := fun x => depsCohs2.(_depsCohs).(_deps).(_restrFrames).2 0 leR_O ζ x)
    (S1 := fun x => (mkDepsCohs depsCohs2).(1).(_deps).(_paintings).2 x)
    (uf0 := fun x => (mkDepsCohs depsCohs2).(1).(_deps).(_restrFrames).2 0 leR_O ζ x)
    (S2 := fun x => (mkPaintings
      (mkDepsRestr (depsCohs := depsCohs2.(_depsCohs).(1));
       mkExtraDeps (depsCohs2.(_depsCohs); depsCohs2.(_extraDepsCohs)))).2 x)
    (fA := ((mkCohFrameTypesAndRestrFrames depsCohs2.(_depsCohs).(_restrPaintings).1)
        .(RestrFramesDef) depsCohs2.(_depsCohs).(_cohs).1).2 q.+1 (⇑ Hq) ε)
    (fB := ((mkCohFrameTypesAndRestrFrames depsCohs2.(_depsCohs).(_restrPaintings).1)
        .(RestrFramesDef) depsCohs2.(_depsCohs).(_cohs).1).2 s.+1 (⇑ (Hs ↕ (Hr ↕ Hq))) θ)
    (fC := ((mkCohFrameTypesAndRestrFrames depsCohs2.(_depsCohs).(_restrPaintings).1)
        .(RestrFramesDef) depsCohs2.(_depsCohs).(_cohs).1).2 r.+1 (⇑ (Hr ↕ Hq)) ω)
    (a := nth l ζ)
    (rfq := fun y => depsCohs2.(_depsCohs).(_deps).(_restrFrames).2 q Hq ε y)
    (rfs := fun y =>
      depsCohs2.(_depsCohs).(_deps).(_restrFrames).2 s (Hs ↕ (Hr ↕ Hq)) θ y)
    (rfr := fun y =>
      depsCohs2.(_depsCohs).(_deps).(_restrFrames).2 r (Hr ↕ Hq) ω y)
    (Fq := fun y c => depsCohs2.(_depsCohs).(_restrPaintings).2 q Hq ε y c)
    (Fs := fun y c =>
      depsCohs2.(_depsCohs).(_restrPaintings).2 s (Hs ↕ (Hr ↕ Hq)) θ y c)
    (Fr := fun y c =>
      depsCohs2.(_depsCohs).(_restrPaintings).2 r (Hr ↕ Hq) ω y c)
    (gq := fun dd => depsCohs2.(_depsCohs).(_cohs).2 q Hq 0 leR_O ε ζ dd)
    (gs := fun dd =>
      depsCohs2.(_depsCohs).(_cohs).2 s (Hs ↕ (Hr ↕ Hq)) 0 leR_O θ ζ dd)
    (gr := fun dd =>
      depsCohs2.(_depsCohs).(_cohs).2 r (Hr ↕ Hq) 0 leR_O ω ζ dd)).
  - now exact (coh2Painting q Hq r Hr s Hs ε ω θ
      (((mkCohFrameTypesAndRestrFrames
          (mkRestrPaintings (mkDepsCohs depsCohs2; mkExtraCohs extraDepsCohs2)).1.1)
        .(RestrFramesDef) ((mkCoh2FrameTypesAndCohFrames
            (mkCohPaintings (depsCohs2; extraDepsCohs2)).1)
          .(CohFramesDef) prevCoh2Frames.1).1).2 0 leR_O ζ d) (nth l ζ)).
  - now apply depsCohs2.(_depsCohs).(_deps).(_frames).2.(GUIP).
Defined.

Fixpoint mkCoh2Frames `{depsCohs2: DepsCohs2 p k}
  (extraDepsCohs2: DepsCohs2Extension p k depsCohs2)
  (coh2Paintings: mkCoh2PaintingTypes extraDepsCohs2):
  mkCoh2FrameTypes (mkCohPaintings extraDepsCohs2).
Proof.
  destruct p.
  - unshelve esplit.
    + now exact tt.
    + intros q Hq r Hr s Hs ε ω θ d.
      now trivial.
  - set (h := mkCoh2Frames p k.+1 depsCohs2.(1)%depscohs2
      (depsCohs2; extraDepsCohs2)%extradepscohs2 coh2Paintings.1).
    unshelve esplit.
    + now exact h.
    + intros q Hq r Hr s Hs ε ω θ [d l].
      unshelve eapply eq_existT_curried_hex.
      * now exact (h.2 q.+1 (⇑ Hq) r.+1 (⇑ Hr) s.+1 (⇑ Hs) ε ω θ d).
      * now exact_no_check (mkCoh2Layer depsCohs2 extraDepsCohs2 h
          coh2Paintings.2 q Hq r Hr s Hs ε ω θ d l).
Defined.

Class DepsCohs3 p k := {
  _depsCohs2: DepsCohs2 p k;
  _extraDepsCohs2: DepsCohs2Extension p k _depsCohs2;
  _coh2Paintings: mkCoh2PaintingTypes _extraDepsCohs2;
}.

#[local]
Instance toDepsCohs3 `{extraDepsCohs2: DepsCohs2Extension p k depsCohs2}
  (coh2Paintings: mkCoh2PaintingTypes extraDepsCohs2): DepsCohs3 p k :=
  {| _coh2Paintings := coh2Paintings |}.

#[local]
Instance proj1DepsCohs3 `(depsCohs3: DepsCohs3 p.+1 k): DepsCohs3 p k.+1 :=
{|
  _depsCohs2 := depsCohs3.(_depsCohs2).(1);
  _extraDepsCohs2 := (depsCohs3.(_depsCohs2); depsCohs3.(_extraDepsCohs2));
  _coh2Paintings := depsCohs3.(_coh2Paintings).1;
|}.

Declare Scope depscohs3_scope.
Delimit Scope depscohs3_scope with depscohs3.
Bind Scope depscohs3_scope with DepsCohs3.
Notation "x .(1)" := (proj1DepsCohs3 x%depscohs3)
  (at level 1, left associativity, format "x .(1)"): depscohs3_scope.

#[local]
Instance mkDepsCohs2 `(depsCohs3: DepsCohs3 p k): DepsCohs2 p.+1 k :=
{|
  _depsCohs := mkDepsCohs depsCohs3.(_depsCohs2);
  _extraDepsCohs := mkExtraCohs depsCohs3.(_extraDepsCohs2);
  _cohPaintings := mkCohPaintings depsCohs3.(_extraDepsCohs2);
  _coh2Frames := mkCoh2Frames depsCohs3.(_extraDepsCohs2) depsCohs3.(_coh2Paintings);
|}.

Inductive DepsCohs3Extension p: forall k (depsCohs3: DepsCohs3 p k), Type :=
| TopCoh3Dep `{depsCohs3: DepsCohs3 p 0}
  (E: mkFrame (mkDepsRestr (depsCohs := mkDepsCohs (mkDepsCohs2 depsCohs3))) -> HGpd)
  : DepsCohs3Extension p 0 depsCohs3
| AddCoh3Dep {k} (depsCohs3: DepsCohs3 p.+1 k):
  DepsCohs3Extension p.+1 k depsCohs3 ->
  DepsCohs3Extension p k.+1 depsCohs3.(1).

Arguments TopCoh3Dep {p depsCohs3}.
Arguments AddCoh3Dep {p k}.

Declare Scope extra_depscohs3_scope.
Delimit Scope extra_depscohs3_scope with extradepscohs3.
Bind Scope extra_depscohs3_scope with DepsCohs3Extension.
Notation "( x ; y )" := (AddCoh3Dep x y)
  (at level 0, format "( x ; y )"): extra_depscohs3_scope.

Fixpoint mkExtraCohs2 `{depsCohs3: DepsCohs3 p k}
  (extraDepsCohs3: DepsCohs3Extension p k depsCohs3):
  DepsCohs2Extension p.+1 k (mkDepsCohs2 depsCohs3).
Proof.
  destruct extraDepsCohs3.
  - now constructor.
  - apply (AddCoh2Dep (mkDepsCohs2 depsCohs3)).
    now exact (mkExtraCohs2 p.+1 k depsCohs3 extraDepsCohs3).
Defined.

Definition mkCoh2Painting `{depsCohs3: DepsCohs3 p k}
  (extraDepsCohs3: DepsCohs3Extension p k depsCohs3):
  mkCoh2PaintingType (mkDepsCohs2 depsCohs3) (mkExtraCohs2 extraDepsCohs3).
Proof.
  intros q Hq r Hr s.
  generalize dependent r.
  generalize dependent q.
  generalize dependent k.
  generalize dependent p.
  induction s as [|s mkCoh2Painting].
  - intros p k depsCohs3 extraDepsCohs3 q Hq r Hr Hs ε ω θ d c.
    unfold mkCoh2PaintingInstanceType, mkCohLayer; cbn.
    rewrite (sigT_fst_lmap2_rew_eq
      (P := fun x => (mkDepsCohs depsCohs3.(_depsCohs2)).(_deps).(_paintings).2 x)
      (rf0 := fun a x => (mkDepsCohs depsCohs3.(_depsCohs2)).(_deps).(_restrFrames).2 0 leR_O a x)).
    now eapply (rew_coh2Painting_restr0
      (P := fun x => mkPainting depsCohs3.(_depsCohs2).(_depsCohs).(_extraDeps) x)
      (S := fun d0 => {a: mkLayer mkRestrFrames.2 d0 &T
        mkPainting (mkExtraDeps depsCohs3.(_depsCohs2).(_extraDepsCohs)) (d0; a)})
      (r0 := fun x =>
        (mkDepsCohs2 depsCohs3).(_depsCohs).(_deps).(_restrFrames).2 0 leR_O θ x)).
  - intros p k depsCohs3 extraDepsCohs3 q Hq r Hr Hs ε ω θ d c.
    destruct r; [now contradiction |].
    destruct q; [now contradiction |].
    destruct extraDepsCohs3; [now contradiction |].
    destruct c as [l c].
    unfold mkCoh2PaintingInstanceType; cbv zeta.
    unshelve eapply (eq_existT_curried_dep_hex
      (A0 := ((mkRestrFrameTypesAndFrames
          (mkDepsCohs2 depsCohs3.(1)).(_depsCohs).(_deps).(_paintings).1)
        .(FrameDef)
          (mkDepsCohs2 depsCohs3.(1)).(_depsCohs).(_deps).(_restrFrames).1).2)
      (B := ((mkRestrFrameTypesAndFrames
          depsCohs3.(_depsCohs2).(_depsCohs).(_deps).(_paintings).1)
        .(FrameDef)
          depsCohs3.(_depsCohs2).(_depsCohs).(_deps).(_restrFrames).1).2)
      (P0 := fun a => (mkLayer
        (mkDepsCohs2 depsCohs3.(1)).(_depsCohs).(_deps).(_restrFrames).2
        a).(GDom))
      (R0 := fun a u => (mkPainting
        (mkDepsCohs2 depsCohs3.(1)).(_depsCohs).(_extraDeps) (a; u)).(GDom))
      (P' := fun b => (mkLayer
        depsCohs3.(_depsCohs2).(_depsCohs).(_deps).(_restrFrames).2 b).(GDom))
      (R' := fun b u => (mkPainting
        depsCohs3.(_depsCohs2).(_depsCohs).(_extraDeps) (b; u)).(GDom))
      ((mkDepsCohs2 depsCohs3.(1)).(_depsCohs).(_deps).(_restrFrames).2
        q.+1 Hq ε)
      (fun d0 l0 => mkRestrLayer
        depsCohs3.(_depsCohs2).(_depsCohs).(_restrPaintings).2
        depsCohs3.(_depsCohs2).(_depsCohs).(_cohs).2 q (⇓ Hq) ε d0 l0)
      (fun d0 l0 c0 => mkRestrPainting
        depsCohs3.(_depsCohs2).(_extraDepsCohs) q (⇓ Hq) ε (d0; l0) c0)
      ((mkDepsCohs2 depsCohs3.(1)).(_depsCohs).(_deps).(_restrFrames).2
        s.+1 (Hs ↕ (Hr ↕ Hq)) θ)
      (fun d0 l0 => mkRestrLayer
        depsCohs3.(_depsCohs2).(_depsCohs).(_restrPaintings).2
        depsCohs3.(_depsCohs2).(_depsCohs).(_cohs).2
        s (⇓ (Hs ↕ (Hr ↕ Hq))) θ d0 l0)
      (fun d0 l0 c0 => mkRestrPainting
        depsCohs3.(_depsCohs2).(_extraDepsCohs)
        s (⇓ (Hs ↕ (Hr ↕ Hq))) θ (d0; l0) c0)
      ((mkDepsCohs2 depsCohs3.(1)).(_depsCohs).(_deps).(_restrFrames).2
        r.+1 (Hr ↕ Hq) ω)
      (fun d0 l0 => mkRestrLayer
        depsCohs3.(_depsCohs2).(_depsCohs).(_restrPaintings).2
        depsCohs3.(_depsCohs2).(_depsCohs).(_cohs).2 r (⇓ (Hr ↕ Hq)) ω d0 l0)
      (fun d0 l0 c0 => mkRestrPainting
        depsCohs3.(_depsCohs2).(_extraDepsCohs) r (⇓ (Hr ↕ Hq)) ω (d0; l0) c0)).
    + now exact (mkCoh2Layer depsCohs3.(_depsCohs2) depsCohs3.(_extraDepsCohs2)
        (mkCoh2Frames (depsCohs3.(_depsCohs2); depsCohs3.(_extraDepsCohs2))
          depsCohs3.(1).(_coh2Paintings))
        depsCohs3.(_coh2Paintings).2 q (⇓ Hq) r (⇓ Hr) s (⇓ Hs) ε ω θ d l).
    + now exact_no_check (mkCoh2Painting p.+1 k depsCohs3 extraDepsCohs3
        q (⇓ Hq) r (⇓ Hr) (⇓ Hs) ε ω θ (d; l) c).
Defined.

Fixpoint mkCoh2Paintings `{depsCohs3: DepsCohs3 p k}
  (extraDepsCohs3: DepsCohs3Extension p k depsCohs3) {struct p}:
  mkCoh2PaintingTypes (mkExtraCohs2 extraDepsCohs3).
Proof.
  destruct p.
  - unshelve esplit. now exact tt.
    now exact (mkCoh2Painting extraDepsCohs3).
  - unshelve esplit. now exact (mkCoh2Paintings p k.+1
      depsCohs3.(1)%depscohs3 (depsCohs3; extraDepsCohs3)%extradepscohs3).
    now exact (mkCoh2Painting extraDepsCohs3).
Defined.

Class νGpdData p := {
  frames: mkFrameTypes p 0;
  paintings: mkPaintingTypes p 0 frames;
  restrFrames: mkRestrFrameTypes paintings;
  restrPaintings E: mkRestrPaintingTypes (TopRestrDep E);
  cohFrames E: mkCohFrameTypes (restrPaintings E);
  cohPaintings E E': mkCohPaintingTypes
    (depsCohs := toDepsCohs (deps := toDepsRestr restrFrames) (cohFrames E))
    (TopCohDep E');
  coh2Frames E E': mkCoh2FrameTypes (cohPaintings E E');
  coh2Paintings E E' E'': mkCoh2PaintingTypes
    (depsCohs2 := toDepsCohs2 (coh2Frames E E'))
    (TopCoh2Dep E'');
}.

Section νGpdData.
Variable p: nat.
Variable C: νGpdData p.
Variable E: mkFrame (toDepsRestr C.(restrFrames)) -> HGpd.

#[local]
Instance mkνGpdData: νGpdData p.+1 :=
{|
  frames := mkFrames _;
  paintings := mkPaintings _;
  restrFrames := mkRestrFrames;
  restrPaintings E' := mkRestrPaintings (TopCohDep E');
  cohFrames E' := mkCohFrames (C.(cohPaintings) E E') (C.(coh2Frames) E E');
  cohPaintings E' E'' := mkCohPaintings
    (TopCoh2Dep (depsCohs2 := toDepsCohs2 (C.(coh2Frames) E E')) E'');
  coh2Frames E' E'' := mkCoh2Frames
    (TopCoh2Dep (depsCohs2 := toDepsCohs2 (C.(coh2Frames) E E')) E'')
    (C.(coh2Paintings) E E' E'');
  coh2Paintings E' E'' E''' := mkCoh2Paintings
    (TopCoh3Dep (depsCohs3 := toDepsCohs3 (C.(coh2Paintings) E E' E'')) E''');
|}.
End νGpdData.

Class νGpd p := {
  prefix: Type;
  data: prefix -> νGpdData p;
}.

(** ************************************************)
(** The construction of [νGpd n+1] from [νGpd n] *)

(** Extending the initial prefix *)
Definition mkPrefix p {C: νGpd p}: Type :=
  { D: C.(prefix) &T mkFrame (toDepsRestr (C.(data) D).(restrFrames)) -> HGpd }.

#[local]
Instance mkνGpd0: νGpd 0.
Proof.
  unshelve esplit.
  - now exact gunit.
  - unshelve esplit; now trivial.
Defined.

#[local]
Instance mkνGpd {p} (C: νGpd p): νGpd p.+1 :=
{|
  prefix := mkPrefix p;
  data := fun D: mkPrefix p => mkνGpdData p (C.(data) D.1) D.2;
|}.

(** An [νGpd] truncated up to dimension [n] *)
Fixpoint νGpdAt n: νGpd n :=
  match n with
  | O => mkνGpd0
  | n.+1 => mkνGpd (νGpdAt n)
  end.

CoInductive νGpdFrom n (X: (νGpdAt n).(prefix)): Type := cons {
  this: mkFrame (toDepsRestr ((νGpdAt n).(data) X).(restrFrames)) -> HGpd;
  next: νGpdFrom n.+1 (X; this);
}.

(** The final construction *)
Definition νGpds := νGpdFrom 0 tt.

End νGpd.

Module νGpdSimplicial := νGpd SimplicialGpdLayer.
Module νGpdCubical := νGpd CubicalGpdLayer.

(** Some example *)

Example SemiSimplicial5 := Eval lazy in (νGpdSimplicial.νGpdAt 5).(νGpdSimplicial.prefix _).
Print SemiSimplicial5.
