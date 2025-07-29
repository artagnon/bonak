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

Fixpoint FrameGen p: Type :=
  match p with
  | 0 => unit
  | S p => { frames'': FrameGen p &T HSet }
  end.

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
| TopPrev: ExtensionGen (n := O)
| AddExtraPrev {n: nat} {frame'': HSet} {painting'': frame'' -> HSet}:
   ExtensionGen (p := p.+1) (frames'' := (frames''; frame''))
     (paintings'' := (paintings''; painting'')) (n := n) ->
   ExtensionGen (frames'' := frames'') (paintings'' := paintings'') (n := n.+1).

(**
Build the list of pairs of the type RestrFrameTypesDef(n+1,p) of
restrFrame(n+1,p) for p <= n and of the definition of frame(n+1,p),
for p <= n+1, in function of effective RestrFrames of these types.

That is, we build for p <= n.+1:
  p = 0 : { restrFrameTypes = unit ; frame(n+1,0)(restrFrames_{0..0-1}) }
  p = 1 : { restrFrameTypes = {_:unit & restrFrameType0 ;
    frame(n+1,1)(restrFrames_{0..0}) }
  ...
  p     : { restrFrameTypes = {RestrFrameType0 ... restrFrameType_{p-1}} ;
    frame_p(restrFrames_{0..p-1}) }
  n+1   : { restrFrameTypes = {RestrFrameType0 ... restrFrameType_n} ;
    frame(n+1,n+1)(restrFrames_{0..n})

Example: if p = 0
  RestrFrameTypesDef := []
  FrameDef [] := [unit] (presented as a Sigma-type, i.e. as "unit")
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
        (frames' R.1; { d: (frames' R.1).2 & hforall ε, paintings''.2 (R.2 O leY_O ε d) }) : FrameGen p.+2
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
  FormDepsExtension (n := O) deps
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
  | TopRestrFrames E' => fun d => E' d
  | AddExtraRestrFrame deps dep extraDeps => fun d =>
      {l: hforall ε, dep.(_painting'') (dep.(_restrFrame') O leY_O ε d) &
       mkPainting' extraDeps (d; l)}
  end.

Definition MatchPainting (loop: forall `{deps: FormDeps p n}
  (extraDeps: FormDepsExtension deps),
  PaintingGen p.+1 (mkFrames' deps)) {p n} :=
  match p return forall `(deps: FormDeps p n)
  (extraDeps: FormDepsExtension deps), PaintingGen p (mkFrames' deps).1 with
  | O => fun _ _ => tt
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
  destruct p; easy.
Defined.

(* Example: if p := 0, extraDeps := ([],E')
   mkRestrFrameTypes := [unit -> unit] *)

Definition mkRestrFrameTypes `(deps: FormDeps p n)
  (extraDeps: FormDepsExtension deps) :=
  (mkRestrFrameTypesAndFrames' (n := n) (mkFrames' deps)
    (mkPaintings' extraDeps)).(RestrFrameTypesDef).

Definition mkPrevRestrFrameTypes `(deps: FormDeps p n)
  (extraDeps: FormDepsExtension deps) :=
  (mkRestrFrameTypesAndFrames' (n := n.+1) (mkFrames' deps).1
    (mkPaintings' extraDeps).1).(RestrFrameTypesDef).

Definition mkDeps `{deps: FormDeps p n}
  (extraDeps: FormDepsExtension deps)
  (restrFrames: mkRestrFrameTypes deps extraDeps) :=
{|
  _frames'' := mkFrames' deps;
  _paintings'' := mkPaintings' extraDeps;
  _restrFrames' := restrFrames;
|}.

Definition mkFrame `{deps: FormDeps p n}
  (extraDeps: FormDepsExtension deps)
  (restrFrames: mkRestrFrameTypes deps extraDeps) :=
  mkFrame' (mkDeps extraDeps restrFrames).

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
  | O =>
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
      CohFrameTypesDef := { Q:
        cohFrameTypes &T
        (* statement of cohFrameType(n+2,p) *)
        forall r q (Hrq: r <= q) (Hq: q <= n) (ε ω: arity) d,
        deps.(_restrFrames').2 q Hq ε ((restrFrames Q).2 r
          (leY_trans Hrq (leY_up Hq)) ω d) =
        deps.(_restrFrames').2 r (leY_trans Hrq Hq) ω ((restrFrames Q).2 q.+1
          (⇑ Hq) ε d) };
      RestrFramesDef Q :=
      (* RestrFrame(n+2,p+1) *)
      let restrFrame q (Hq: q <= n) ε
        (d: mkFrame (deps.(2); extraDeps) (restrFrames Q.1)) :=
          ((restrFrames Q.1).2 q.+1 (⇑ Hq) ε d.1 as rf in _;
           fun ω => rew [deps.(_paintings'').2] Q.2 O q leY_O Hq ε ω d.1 in
            restrPaintings'.2 q _ ε _
              (rew unfoldPaintingProj (deps.(2); extraDeps) _ in d.2 ω)
           in forall ω, deps.(_paintings'').2 (deps.(_restrFrames').2  _ _ _ rf))
      in (restrFrames Q.1 as rf in _;
          restrFrame in forall q Hq ω,
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

Definition mkRestrFrame `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  (restrPaintings': RestrPaintingTypes' extraDeps) cohs:
  forall q {Hq: q <= n} ε,
    mkPrevFrame extraDeps (mkRestrFrames restrPaintings' cohs) ->
    mkFrame' deps :=
    (mkRestrFrames restrPaintings' cohs).2.

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
  {restrPaintings': RestrPaintingTypes' (dep; extraDeps)}
  (cohs: mkCohFrameTypes restrPaintings') :=
  let restrFrame := (mkRestrFrames restrPaintings' cohs).2 in
  forall r q (Hrq: r <= q) (Hq: q <= n) (ε ω: arity) d,
      dep.(_restrFrame') q Hq ε (restrFrame r (leY_trans Hrq (leY_up Hq)) ω d)
      = dep.(_restrFrame') r (leY_trans Hrq Hq) ω (restrFrame q.+1 (⇑ Hq) ε d).

Inductive CohFramesExtension {p}: forall `(deps: FormDeps p n)
  (extraDeps: FormDepsExtension deps)
  (restrPaintings': RestrPaintingTypes' extraDeps),
  mkCohFrameTypes restrPaintings' -> Type :=
| TopCoh
    {deps}
    {E': mkFrame' deps -> HSet}
    {restrPaintings'}
    {cohs: mkCohFrameTypes _}
    {E: mkFrame _ (mkRestrFrames restrPaintings' cohs) -> HSet}
    : CohFramesExtension (n := O) deps (TopRestrFrames E') restrPaintings' cohs
| AddCohFrame {n deps dep extraDeps}
    {restrPaintings': RestrPaintingTypes' (dep; extraDeps)}
    {restrPainting': RestrPaintingType' dep extraDeps}
    {cohs: mkCohFrameTypes restrPaintings'}
    (coh: mkCohFrameType cohs):
    CohFramesExtension (deps; dep) extraDeps
      (restrPaintings'; restrPainting') (cohs; coh) ->
      CohFramesExtension (n := n.+1) deps (dep; extraDeps) restrPaintings' cohs.

Declare Scope extra_cohs_scope.
Delimit Scope extra_cohs_scope with extracohs.
Bind Scope extra_cohs_scope with CohFramesExtension.
Notation "( x ; y )" := (AddCohFrame x y)
  (at level 0, format "( x ; y )"): extra_cohs_scope.

Fixpoint mkExtraDeps `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  {cohs: mkCohFrameTypes restrPaintings'}
  (extraCohs: CohFramesExtension deps extraDeps restrPaintings' cohs):
  FormDepsExtension (mkFullDeps restrPaintings' cohs).
Proof.
  destruct extraCohs.
  - now constructor.
  - unshelve econstructor.
    + now apply (mkFullDeps (extraDeps := extraDeps) (restrPaintings'; restrPainting') (cohs; coh)).(2).
    + now apply (mkExtraDeps p.+1 n (deps; dep)%deps extraDeps
      (restrPaintings'; restrPainting') (cohs; coh) extraCohs).
Defined.

Definition mkPainting `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  {cohs: mkCohFrameTypes restrPaintings'}
  (extraCohs: CohFramesExtension deps extraDeps restrPaintings' cohs) :=
  mkPainting' (mkExtraDeps extraCohs):
  mkFrame (p := p) extraDeps _ -> HSet.

Definition mkPrevPainting `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  {cohs: mkCohFrameTypes restrPaintings'}
  (extraCohs: CohFramesExtension deps extraDeps restrPaintings' cohs) :=
  mkPainting'
    ((mkFullDeps restrPaintings' cohs).(2);
      mkExtraDeps extraCohs)%extradeps:
    mkPrevFrame (p := p) extraDeps (mkRestrFrames restrPaintings' cohs) -> HSet.

Fixpoint mkRestrPainting `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  (cohs: mkCohFrameTypes restrPaintings')
  (extraCohs: CohFramesExtension deps extraDeps restrPaintings' cohs):
  forall q {Hq: q <= n} ε d, mkPrevPainting extraCohs d ->
    mkPainting' extraDeps (mkRestrFrame restrPaintings' cohs q ε d).
Proof.
  destruct extraCohs, q.
  - intros * (l, _). now apply (rew unfoldPaintingProj _ _ in l ε).
  - intros. exfalso. now apply leY_O_contra in Hq.
  - intros * (l, _). now apply (rew unfoldPaintingProj _ _ in l ε).
  - intros * (l, c). unshelve esplit.
    + intro ω. rewrite <- coh with (Hrq := leY_O) (Hq := ⇓ Hq).
      apply restrPainting'. simpl in l.
      now apply (rew unfoldPaintingProj _ _ in l ω).
    + intros *. apply (mkRestrPainting _ _ _ extraDeps (restrPaintings';restrPainting') (cohs; coh) _ q (⇓ Hq) ε (d as x in _; l in _) c).
Defined.

Definition mkRestrPaintingTypes `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  (cohs: mkCohFrameTypes restrPaintings')
  (extraCohs: CohFramesExtension deps extraDeps restrPaintings' cohs) :=
  RestrPaintingTypes' (mkExtraDeps extraCohs).

Fixpoint mkRestrPaintings `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  (cohs: mkCohFrameTypes restrPaintings')
  (extraCohs: CohFramesExtension deps extraDeps restrPaintings' cohs):
  mkRestrPaintingTypes cohs extraCohs.
destruct p.
- red. simpl.
  + esplit.
  exact tt.
  red; intros * c. simpl.
  eapply (mkRestrPainting cohs extraCohs q ε), c.
- esplit.
  + apply (mkRestrPaintings p n.+1 _ _ _ cohs.1 (cohs.2; extraCohs)%extracohs).
  + red; intros * c. simpl. eapply (mkRestrPainting cohs extraCohs), c.
Defined.

Definition CohPaintingType `{deps: FormDeps p n.+1}
  {dep: FormDep deps}
  {extraDeps: FormDepsExtension (deps; dep)}
  {restrPaintings': RestrPaintingTypes' (dep; extraDeps)}
  {restrPainting': RestrPaintingType' dep extraDeps}
  {cohs: mkCohFrameTypes restrPaintings'}
  (coh: mkCohFrameType cohs)
  (extraCohs: CohFramesExtension (deps; dep) extraDeps
    (restrPaintings'; restrPainting')
    (cohs; coh)) :=
  forall r q (Hrq: r <= q) (Hq: q <= n) (ε ω: arity) d c,
  rew [dep.(_painting'')] coh r q Hrq Hq ε ω d in
  restrPainting' q _ ε _ (mkRestrPainting cohs (coh; extraCohs) r ω d c) =
  restrPainting' r _ ω _ (mkRestrPainting cohs (coh; extraCohs) q.+1 ε d c).

Fixpoint CohPaintingTypes {p}:
  forall `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  {cohs: mkCohFrameTypes restrPaintings'}
  (extraCohs: CohFramesExtension deps extraDeps restrPaintings' cohs),
  Type :=
  match p with
  | O => fun _ _ _ _ _ _ => unit
  | S p =>
    fun n deps extraDeps restrPaintings' cohs extraCohs =>
    { R: CohPaintingTypes (cohs.2; extraCohs) &T
         CohPaintingType cohs.2 extraCohs }
  end.

Fixpoint mkCohFrames `{deps: FormDeps p n}
  {extraDeps: FormDepsExtension deps}
  {restrPaintings': RestrPaintingTypes' extraDeps}
  (cohs: mkCohFrameTypes restrPaintings')
  (extraCohs: CohFramesExtension deps extraDeps restrPaintings' cohs)
  (cohPaintings: CohPaintingTypes extraCohs)
  {struct p}:
  mkCohFrameTypes (mkRestrPaintings cohs extraCohs).
Proof.
destruct p.
- red. simpl.
  esplit. exact tt.
  intros. reflexivity.
- unshelve esplit.
  + apply (mkCohFrames p _ _ _ restrPaintings'.1 cohs.1 (cohs.2; extraCohs)%extracohs cohPaintings.1).
  + intros. unshelve eapply eq_existT_curried.
    * eapply ((mkCohFrames p _ _ _ restrPaintings'.1 cohs.1 (cohs.2; extraCohs)%extracohs cohPaintings.1).2 r.+1 q.+1 _ _ ε ω).
    * apply (cohPaintings.2 r q _ _ ε ω).
Admitted.

Class νTypeAux p := {
  deps: FormDeps p 0;
  restrPaintings' E': RestrPaintingTypes' (TopRestrFrames E');
  cohFrames E': mkCohFrameTypes (restrPaintings' E');
}.
(*
  cohPainting {E'} {p} {Hp: p.+1 <~ n.+1} r q {Hpq: p.+1 <~ q.+1}
    {Hpr: p.+2 <~ r.+2}
    {Hrq: r <~ q} {Hr: r.+2 <~ n.+2} {Hq: q.+1 <~ n.+1} {ε ω E}
    {d: frame p} (c: painting p d (E := E) (E' := E')
      (Hp := leI_down (leI_down (leI_trans Hpr Hr)))):
    rew [painting'' p] cohFrame r q d (Hpr := leI_lower_both Hpr)
      (Hrq := leI_raise_both Hrq) in
    restrPainting' p q ε (restrPainting p r ω c
      (Hq := leI_down (leI_lower_both Hr))) =
    restrPainting' p r ω (restrPainting p q.+1 ε c
      (Hpq := leI_down Hpq) (Hq := Hq));
}. *)

Class νType p := {
  prefix'': Type;
  data: prefix'' -> νTypeAux p;
}.

(***************************************************)
(** The construction of [νType n+1] from [νType n] *)

(** Extending the initial prefix *)
Definition mkPrefix'' p {C: νType p}: Type :=
  { D: C.(prefix'') &T
    mkFrame' (n := O) (C.(data) D).(deps) -> HSet }.

Section νTypeData.
Variable p: nat.
Variable C: νType p.
Variable D: mkPrefix'' p.

Definition mkDeps': FormDeps p.+1 0 :=
  mkFullDeps _ ((C.(data) D.1).(cohFrames) D.2).

Definition mkRestrPaintings' E': RestrPaintingTypes' _ _ :=
  mkRestrPaintings
  ((C.(data) D.1).(cohFrames) D.2) (TopCoh (E' := D.2) (E := E')).

Definition mkCohFrames' E' : mkCohFrameTypes (mkRestrPaintings' E') :=
  mkCohFrames ((C.(data) D.1).(cohFrames) D.2) (TopCoh (E' := D.2) (E := E')).

End νTypeData.

#[local]
Instance mkνType p {C: νType p}: νType p.+1.
  unshelve esplit.
  now exact (mkPrefix'' p).
  intro D. unshelve esplit.
  now eapply mkDeps'.
  now apply mkRestrPaintings'.
  now apply mkCohFrames'.
Defined.

End νType.
