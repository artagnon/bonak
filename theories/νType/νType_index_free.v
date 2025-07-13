Require Import List.
Import Logic.EqNotations ListNotations.
Require Import Logic.FunctionalExtensionality.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT Notation RewLemmas HSet LeYoneda.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Remove Printing Let sigT.
Remove Printing Let prod.

Section νType.
Variable arity: HSet.

Section RestrFramesDef.

Inductive PrevLevel :=
| EmptyPrev: PrevLevel
| AddPrev (Frame: HSet) (Painting: Frame -> HSet) (rest: PrevLevel): PrevLevel.

Class RestrFrameTypeBlock := {
  RestrFrameTypesDef: Type;
  FrameDef: RestrFrameTypesDef -> HSet;
}.

Inductive PrevExtension {Prev}: forall {n: nat}, Type :=
| TopPrev: PrevExtension (n := O)
| AddExtraPrev {n: nat} {Frame: HSet} {Painting: Frame -> HSet}:
   PrevExtension (Prev := AddPrev Frame Painting Prev) (n := n) ->
   PrevExtension (n := n.+1).

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

Example: if Prev = EmptyPrev
  RestrFrameTypesDef := []
  FrameDef [] := [unit] (presented as a Sigma-type, i.e. as "unit")
*)
Fixpoint mkRestrFrameTypesAndFrames' {Prev n}: RestrFrameTypeBlock :=
  match Prev with
  | EmptyPrev =>
    {|
      RestrFrameTypesDef := unit;
      FrameDef _ := hunit
    |}
  | AddPrev FramePrev PaintingPrev Prev =>
    {|
      RestrFrameTypesDef :=
        { R: (mkRestrFrameTypesAndFrames').(RestrFrameTypesDef) &T
          forall q (Hq: q <= n) (ε: arity),
          (mkRestrFrameTypesAndFrames' (n := n.+1)).(FrameDef) R -> FramePrev };
      FrameDef R :=
        { d: (mkRestrFrameTypesAndFrames' (Prev := Prev)).(FrameDef) R.1 &
          hforall ε, PaintingPrev (R.2 O leY_O ε d) }
    |}
  end.

Definition mkRestrFrameTypes' {Prev n} :=
  (mkRestrFrameTypesAndFrames' (Prev := Prev) (n := n)).(RestrFrameTypesDef).

Definition mkFrameOfRestrFrames' {Prev n}: mkRestrFrameTypes' -> HSet :=
  (mkRestrFrameTypesAndFrames' (Prev := Prev) (n := n)).(FrameDef).

Inductive RestrFramesExtension {Prev}: forall {n}
  (restrs: mkRestrFrameTypes' (Prev := Prev)), PrevExtension -> Type :=
| TopRestrFrames {restrs'}:
  forall E': mkFrameOfRestrFrames' (n := O) restrs' -> HSet,
  RestrFramesExtension (n := O) restrs' TopPrev
| AddExtraRestrFrame {n FramePrev PaintingPrev extraPrev restrs'}:
  forall restr': forall q (Hq: q <= n) (ε: arity),
          mkFrameOfRestrFrames' (n := n.+1) restrs' -> FramePrev.(Dom),
  RestrFramesExtension (Prev := AddPrev FramePrev PaintingPrev Prev)
    (restrs'; restr') extraPrev ->
    RestrFramesExtension (n := n.+1) restrs' (AddExtraPrev (Prev := Prev) extraPrev).

(* Example: if Prev := EmptyPrev, extraPrev := [], extraRestrs' := ([],E)
   mkPainting:= [E] *)

Fixpoint mkPainting' {Prev n} (restrs': mkRestrFrameTypes' (Prev := Prev))
  extraPrev (extraRestrs': RestrFramesExtension restrs' extraPrev):
  mkFrameOfRestrFrames' restrs' -> HSet :=
  match extraRestrs' in RestrFramesExtension restrs' extraPrev
     return mkFrameOfRestrFrames' restrs' -> HSet
  with
  | TopRestrFrames E => fun d => E d
  | @AddExtraRestrFrame _ n FramePrev PaintingPrev extraPrev restrs'
    restr' extraRestrs' => fun d =>
      {l: hforall ε, PaintingPrev (restr' O leY_O ε d) &
      mkPainting' (Prev := AddPrev FramePrev PaintingPrev Prev)
        (restrs'; restr') extraPrev extraRestrs' (d; l)}
  end.

Definition MatchPrev
  (loop: forall Prev n (restrs': mkRestrFrameTypes' (Prev := Prev))
  extraPrev (extraRestrs': RestrFramesExtension restrs' extraPrev), PrevLevel)
  {Prev} :=
  match Prev return forall n (restrs': mkRestrFrameTypes' (Prev := Prev))
  extraPrev (extraRestrs': RestrFramesExtension (n := n) restrs' extraPrev),
  PrevLevel
  with
  | EmptyPrev => fun _ _ _ _ => EmptyPrev
  | AddPrev FramePrev PaintingPrev Prev =>
    fun n restrs' extraPrev extraRestrs' =>
    loop Prev n.+1 restrs'.1 (AddExtraPrev extraPrev)
      (AddExtraRestrFrame (restrs' := restrs'.1) restrs'.2 extraRestrs')
  end.

Fixpoint mkLevelRec Prev n (restrs': mkRestrFrameTypes')
  extraPrev (extraRestrs': RestrFramesExtension restrs' extraPrev):
  PrevLevel :=
  AddPrev (mkFrameOfRestrFrames' restrs')
    (mkPainting' restrs' extraPrev extraRestrs')
    (MatchPrev mkLevelRec n restrs' extraPrev extraRestrs').

(* Example: if Prev := EmptyPrev, extraPrev := [], extraRestrs' := ([],E)
   mkLevel := [{frame:=unit;painting:=E}] *)

Definition mkLevel {Prev n} (restrs': mkRestrFrameTypes' (Prev := Prev))
  extraPrev (extraRestrs': RestrFramesExtension restrs' extraPrev):
  PrevLevel :=
  AddPrev (mkFrameOfRestrFrames' restrs')
    (mkPainting' restrs' extraPrev extraRestrs')
    (MatchPrev mkLevelRec n restrs' extraPrev extraRestrs').

(* Example: if Prev := EmptyPrev, extraPrev := [], extraRestrs' := ([],E)
   mkRestrFrameTypes := [unit -> unit] *)

Definition mkRestrFrameTypes {Prev n restrs' extraPrev extraRestrs'} :=
  (mkRestrFrameTypesAndFrames'
    (Prev := mkLevel (Prev := Prev) (n := n) restrs' extraPrev
      extraRestrs') (n := n)).(RestrFrameTypesDef).

Definition mkPrevRestrFrameTypes {Prev n restrs' extraPrev extraRestrs'} :=
  (mkRestrFrameTypesAndFrames'
    (Prev := MatchPrev mkLevelRec (Prev := Prev) n restrs' extraPrev
      extraRestrs') (n := n.+1)).(RestrFrameTypesDef).

(* Example: if Prev := EmptyPrev, extraPrev := [], extraRestrs' := ([],E)
   mkFrameOfRestrFrames [restr: unit -> unt] := [unit; \().∀ω.E(restr())]
      (presented as a Sigma-type, i.e. {d:unit & ∀ω.E(restr())} *)

Definition mkFrameOfRestrFrames {Prev n restrs' extraPrev extraRestrs'}
  : mkRestrFrameTypes (Prev := Prev) (n := n) -> HSet :=
    mkFrameOfRestrFrames' (Prev := mkLevel restrs' extraPrev extraRestrs').

Definition mkPrevFrameOfRestrFrames {Prev n restrs' extraPrev extraRestrs'}:
  mkPrevRestrFrameTypes (Prev := Prev) -> HSet :=
  mkFrameOfRestrFrames'
    (Prev := MatchPrev mkLevelRec n restrs' extraPrev extraRestrs').

(* Examples *)
Check fun E restr => eq_refl:
  (mkFrameOfRestrFrames'
      (Prev := AddPrev hunit (fun d: hunit => E d) EmptyPrev) restr).(Dom) =
  {a : unit &T forall a0 : arity, E (restr.2 0 leY_O a0 a)}.
Check fun E' restr E => eq_refl:
  mkPainting' (Prev := AddPrev hunit (fun d => E' d) EmptyPrev)
  restr TopPrev (TopRestrFrames E)
  = fun (d : {a : unit &T forall a0 : arity, E' (restr.2 0 leY_O a0 a)}) => E d.
Check eq_refl : mkRestrFrameTypes' (Prev := EmptyPrev) = unit.
Check eq_refl : mkRestrFrameTypes (Prev := EmptyPrev) (restrs' := tt)
  (extraPrev := TopPrev) (extraRestrs' := TopRestrFrames _) =
                       {_ : unit &T forall q: nat, q <= 0 -> arity -> unit -> unit}.
Check fun E' restr E => eq_refl :
  mkRestrFrameTypes (Prev := AddPrev hunit (fun d => E' d) EmptyPrev)
    (restrs' := restr) (extraPrev := TopPrev) (extraRestrs' := TopRestrFrames E)
  = {R : {_ : unit &T forall q: nat, q <= 1 -> arity -> unit -> unit} &T
      forall q : nat, q <= 0 -> arity ->
       {a : unit &T forall a0: arity, {a1 : forall a1: arity, E' (restr.2 0 leY_O a1 (R.2 0 leY_O a0 a)) &T E (R.2 0 leY_O a0 a; a1)}} ->
       {a : unit &T forall a0: arity, E' (restr.2 0 leY_O a0 a)}}.

Class CohFrameTypeBlock {Prev n restrs extraPrev extraRestrs} := {
  CohFrameTypesDef: Type;
  RestrFramesDef: CohFrameTypesDef ->
    mkRestrFrameTypes (Prev := Prev) (n := n) (restrs' := restrs)
    (extraPrev := extraPrev) (extraRestrs' := extraRestrs)
}.

Variable RestrPainting': forall {Prev n} {FramePrev: HSet}
  {PaintingPrev: FramePrev -> HSet}
  {restrFrames':
    mkRestrFrameTypes' (Prev := AddPrev FramePrev PaintingPrev Prev)}
  {extraPrev: PrevExtension (Prev := AddPrev FramePrev PaintingPrev Prev)}
  {extraRestrs': RestrFramesExtension restrFrames'.1
    (AddExtraPrev extraPrev)}
  q {Hq: q <= n} ε (d: mkFrameOfRestrFrames' restrFrames'.1),
  mkPainting' restrFrames'.1 (AddExtraPrev extraPrev) extraRestrs' d ->
  PaintingPrev (restrFrames'.2 q Hq ε d).

Definition coerce {Prev n}: forall restrFrames' extraPrev extraRestrs,
  mkLevel restrFrames' extraPrev extraRestrs =
  mkLevelRec Prev n restrFrames' extraPrev extraRestrs :=
  match Prev with
  | EmptyPrev => fun _ _ _ => eq_refl
  | AddPrev Frame Painting rest => fun _ _ _ => eq_refl
  end.

#[local]
Instance mkCohFrameTypesAndRestrFrames:
  forall {Prev n} (restrFrames' : mkRestrFrameTypes' (Prev := Prev)) extraPrev
  (extraRestrs': RestrFramesExtension restrFrames' extraPrev),
    CohFrameTypeBlock :=
  fix mkCohFrameTypesAndRestrFrames {Prev}:
  forall n (restrFrames' : mkRestrFrameTypes' (Prev := Prev))
    extraPrev
    (extraRestrs': RestrFramesExtension restrFrames' extraPrev),
    CohFrameTypeBlock :=
  match Prev return forall n (restrFrames' : mkRestrFrameTypes' (Prev := Prev))
    extraPrev
    (extraRestrs': RestrFramesExtension (n := n) restrFrames' extraPrev),
    CohFrameTypeBlock
  with
  | EmptyPrev =>
    fun n restrFrames' extraPrev extraRestrs' =>
    {|
      CohFrameTypesDef := unit;
      RestrFramesDef _ := (tt; fun _ _ _ _ => tt):
        mkRestrFrameTypes (Prev := EmptyPrev) (restrs' := restrFrames')
        (extraPrev := extraPrev) (extraRestrs' := extraRestrs')
    |}
  | AddPrev FramePrev PaintingPrev Prev =>
    fun n restrFrames' extraPrev extraRestrs' =>
    let restrFrames := (mkCohFrameTypesAndRestrFrames n.+1 restrFrames'.1
    (AddExtraPrev extraPrev)
    (AddExtraRestrFrame restrFrames'.2 extraRestrs')).(RestrFramesDef) in
    let cohFrameTypes := (mkCohFrameTypesAndRestrFrames n.+1 restrFrames'.1
    (AddExtraPrev extraPrev)
    (AddExtraRestrFrame restrFrames'.2 extraRestrs')).(CohFrameTypesDef) in
    {|
      CohFrameTypesDef := { Q:
        cohFrameTypes &T
        (* statement of cohFrameType(n+2,p) *)
        forall r q (Hrq: r <= q) (Hq: q <= n) (ε ω: arity) d,
        restrFrames'.2 q Hq ε ((restrFrames Q).2 r
          (leY_trans Hrq (leY_up Hq)) ω d) =
        restrFrames'.2 r (leY_trans Hrq Hq) ω ((restrFrames Q).2 q.+1
          (⇑ Hq) ε d) };
      RestrFramesDef Q :=
      (* RestrFrame(n+2,p+1) *)
      let restrFrame q (Hq: q <= n) ε
        (d: mkFrameOfRestrFrames _) :=
        ((restrFrames Q.1).2 q.+1 (⇑ Hq) ε d.1 as rf in _;
        fun ω => rew [PaintingPrev] Q.2 O q leY_O Hq ε ω d.1 in
          RestrPainting' q ε _ (d.2 ω)
          in forall ω, PaintingPrev (restrFrames'.2  _ _ _ rf))
      in rew [ fun L => {
               R &T forall ω : nat, ω <= n -> arity ->
               mkFrameOfRestrFrames' (Prev := L) R ->
              _} ] coerce _ _ _ in
          (restrFrames Q.1 as rf in _;
           restrFrame in forall q Hq ω, (mkFrameOfRestrFrames rf) -> _)
          : mkRestrFrameTypes (Prev := AddPrev FramePrev PaintingPrev Prev)
    |}
  end.

(* Example: if Prev := EmptyPrev, extraPrev := [], extraRestrs' := ([],E)
   mkCohFrameTypes := [] *)

Definition mkCohFrameTypes {Prev n restrFrames' extraPrev extraRestrs'} :=
  (mkCohFrameTypesAndRestrFrames (Prev := Prev) (n := n) restrFrames' extraPrev
    extraRestrs').(CohFrameTypesDef).

(* Example: if Prev := EmptyPrev, extraPrev := [], extraRestrs' := ([],E)
   mkRestrFramesFrom := [] *)

Definition mkRestrFramesFrom {Prev n} restrFrames' extraPrev extraRestrs' :=
  (mkCohFrameTypesAndRestrFrames (Prev := Prev) (n := n) restrFrames' extraPrev
    extraRestrs').(RestrFramesDef).

Definition mkPrevRestrFramesFrom {Prev n} restrFrames' extraPrev
  extraRestrs' cohs :=
  (mkRestrFramesFrom (Prev := Prev) (n := n) restrFrames' extraPrev
    extraRestrs' cohs).1.

(* Example: if Prev := EmptyPrev, extraPrev := [], extraRestrs' := ([],E) cohs=[]
   then mkLevel := [{frame:=unit;painting:=E}] and
   mkRestrFrameFrom := [\qω().()]
      (presented as a dependent pair, i.e. ((),\qω().()) *)

Definition mkRestrFrameFrom {Prev n restrFrames' extraPrev extraRestrs' cohs}:
  forall q {Hq: q <= n} ε,
    mkPrevFrameOfRestrFrames
      (mkPrevRestrFramesFrom restrFrames' extraPrev extraRestrs' cohs) ->
    mkFrameOfRestrFrames' (Prev := Prev) restrFrames' :=
    (mkRestrFramesFrom restrFrames' extraPrev extraRestrs' cohs).2.

Inductive CohFramesExtension {Prev}: forall {n}
  (restrs': mkRestrFrameTypes' (Prev := Prev))
  (extraPrev: PrevExtension)
  (extraRestrs': RestrFramesExtension restrs' extraPrev),
  mkCohFrameTypes -> Type :=
| TopCoh
    {restrs'}
    {E': mkFrameOfRestrFrames' restrs' -> HSet}
    {cohs: mkCohFrameTypes (extraRestrs' := TopRestrFrames E')}
    {E: mkFrameOfRestrFrames
      (mkRestrFramesFrom restrs' TopPrev (TopRestrFrames E') cohs) -> HSet}
    : CohFramesExtension (n := O) restrs' TopPrev (TopRestrFrames E') cohs
| AddCohFrame {n FramePrev PaintingPrev}
    {extraPrev: PrevExtension (Prev := AddPrev FramePrev PaintingPrev Prev)}
    {restrs': mkRestrFrameTypes'}
    {restr': forall q (Hq: q <= n) (ε: arity),
          mkFrameOfRestrFrames' restrs' -> FramePrev.(Dom)}
    {extraRestrs': RestrFramesExtension
      (Prev := AddPrev FramePrev PaintingPrev Prev)
      (restrs'; restr') extraPrev}
    {cohs}:
    let restrFrames cohs :=
       mkRestrFramesFrom (n := n.+1) restrs' (AddExtraPrev extraPrev)
        (AddExtraRestrFrame restr' extraRestrs') cohs:
        mkRestrFrameTypes (restrs' := restrs')
        (extraPrev := AddExtraPrev extraPrev)
        (extraRestrs' := AddExtraRestrFrame restr' extraRestrs') in
   let restrFrame cohs := (restrFrames cohs).2 in
   forall coh: forall r q (Hrq: r <= q) (Hq: q <= n) (ε ω: arity) d,
          restr' q Hq ε (restrFrame cohs r (leY_trans Hrq (leY_up Hq)) ω d)
          = restr' r (leY_trans Hrq ( Hq)) ω (restrFrame cohs q.+1 (⇑ Hq) ε d),
  CohFramesExtension (Prev := AddPrev FramePrev PaintingPrev Prev)
    (restrs'; restr') extraPrev extraRestrs'
    (cohs as cs in _ ; coh in
      forall r q Hrq Hq ε ω d, restr' q Hq ε (restrFrame cs r _ _ d) = _) ->
      CohFramesExtension (n := n.+1) restrs' (AddExtraPrev extraPrev)
        (AddExtraRestrFrame restr' extraRestrs') cohs.

Fixpoint mkExtension {Prev n} {restrs': mkRestrFrameTypes' (Prev := Prev)}
  {extraPrev} {extraRestrs': RestrFramesExtension (n := n) restrs' extraPrev}:
  PrevExtension (Prev := mkLevel restrs' extraPrev extraRestrs') (n := n).
Proof.
  induction extraRestrs'.
  - now constructor.
  - econstructor. rewrite coerce.
    now eapply (mkExtension (AddPrev FramePrev PaintingPrev Prev) n
      (restrs'; restr')).
Defined.

(* Example: if Prev := EmptyPrev, extraPrev := [], extraRestrs' := ([],E) cohs=[]
   then mkLevel := [{frame:=unit;painting:=E}] and
   mkRestrFramesExtension := ... *)

Definition mkRestrFramesExtension {Prev n}
  {restrs': mkRestrFrameTypes' (Prev := Prev)}
  {extraPrev: PrevExtension} {extraRestrs' cohs}
  (extraCohs: CohFramesExtension (n := n) restrs' extraPrev extraRestrs' cohs):
  RestrFramesExtension (Prev := mkLevel restrs' extraPrev extraRestrs')
    (mkRestrFramesFrom restrs' extraPrev extraRestrs' cohs) mkExtension.
Proof.
  induction extraCohs.
  - constructor. now apply E.
  - unshelve econstructor.
    + (* The extra restr *)
      intros q Hq ε d. apply (mkRestrFrameFrom (extraPrev := extraPrev)
      (extraRestrs' := extraRestrs') (cohs := (cohs; coh)) q ε).
      unfold mkPrevFrameOfRestrFrames, mkPrevRestrFramesFrom.
      unfold mkRestrFramesFrom. simpl. destruct coerce. now apply d.
    + (* The extra restr extension *)
      destruct Prev; now exact IHextraCohs.
Qed.

Definition mkPainting {Prev n restrs' extraPrev extraRestrs' cohs extraCohs} :=
  mkPainting' (Prev := mkLevel restrs' extraPrev extraRestrs')
    (mkRestrFramesFrom restrs' extraPrev extraRestrs' cohs)
    mkExtension (mkRestrFramesExtension extraCohs):
  mkFrameOfRestrFrames (Prev := Prev) (n := n) _ -> HSet.

Definition mkPrevPainting {Prev n restrs' extraPrev extraRestrs'
  cohs extraCohs} :=
  mkPainting' (mkPrevRestrFramesFrom restrs' extraPrev extraRestrs' cohs)
    (AddExtraPrev mkExtension)
    (AddExtraRestrFrame mkRestrFrameFrom (mkRestrFramesExtension extraCohs)):
    mkPrevFrameOfRestrFrames (Prev := Prev) (n := n)
      (mkPrevRestrFramesFrom restrs' extraPrev extraRestrs' cohs) -> HSet.

Definition RestrPainting {Prev n restrs' extraPrev extraRestrs'
  cohs extraCohs}: forall q {Hq: q <= n} ε d, mkPrevPainting
  (extraCohs := extraCohs) d -> mkPainting' (Prev := Prev) restrs'
  extraPrev extraRestrs' (mkRestrFrameFrom (extraPrev := extraPrev)
  (extraRestrs' := extraRestrs') (cohs := cohs) q ε d).
Proof.
  intros * (l, _). destruct q. now apply (l ε). induction extraCohs.
  - exfalso. now apply leY_O_contra in Hq.
  - unshelve esplit.
    + intro ω.
      rewrite <- coh with (Hrq := leY_O) (Hq := ⇓ Hq).
      apply (RestrPainting'
       (restrFrames' := (restrs'; restr'))
       (extraRestrs' := AddExtraRestrFrame restr' extraRestrs')).
      apply l.
    + admit.
Admitted.

Class νTypeAux := {
  prev: PrevLevel;
  restrFrames': mkRestrFrameTypes' (n := 0);
  restrPainting' {n} E' {FramePrev: HSet}
  {PaintingPrev: FramePrev -> HSet}
  {restrFrame': forall q {Hq: q <= n} (ε: arity)
    (d: mkFrameOfRestrFrames' restrFrames'), FramePrev}
  q {Hq: q <= n} ε (d: mkFrameOfRestrFrames' restrFrames'):
    mkPainting' (Prev := prev) restrFrames' TopPrev (TopRestrFrames E') d ->
    PaintingPrev (restrFrame' q ε d);
  cohFrames E':
    mkCohFrameTypes (Prev := prev) (restrFrames' := restrFrames') (n := 0) (extraPrev := TopPrev)
    (extraRestrs' := TopRestrFrames E');
}.
  (* frame {E'} p {Hp: p <~ n.+2}: HSet :=
    Frame n frame'' painting'' restrFrames' E' restrPainting'
    cohFrames p (Hp := Hp);
  restrFrame {E'} p {Hp: p.+1 <~ n.+2} q {Hpq: p <~ q} {Hq: q <~ n.+1}
    ε (d: frame p): frame' p :=
    RestrFrameFromFull n frame'' painting'' restrFrames' E' restrPainting'
    cohFrames p q ε d (Hp := Hp) (Hpq := Hpq) (Hq := Hq);
  cohFrameType {E'} {p} {Hp: p.+2 <~ n.+2} {r q} {Hpq: p.+1 <~ q.+1}
    {Hpr: p.+1 <~ r.+1} {Hrq: r.+1 <~ q.+1} {Hr: r.+1 <~ n.+1}
    {Hq: q.+1 <~ n.+1} {ε ω d} :=
    restrFrame' p q ε (restrFrame p r ω d
      (Hp := leI_down Hp) (Hpq := leI_lower_both Hpr) (Hq := leI_down Hr)) =
    restrFrame' p r ω (restrFrame p q.+1 ε d);
  cohFrame {E'} {p} {Hp: p.+2 <~ n.+2} r q {Hpq: p.+1 <~ q.+1}
    {Hpr Hrq Hr Hq} {ε ω} d:
    cohFrameType (Hpq := Hpq) (Hrq := Hrq) :=
    CohFrame n frame'' painting'' restrFrames' E' restrPainting'
    cohFrames (Hp := Hp) (Hpr := Hpr) (Hrq := Hrq)
    (Hr := Hr) (Hq := Hq) (ε := ε) (ω := ω) r q d;
  painting {E'} p {Hp: p <~ n.+2} {E} (d: frame p): HSet :=
    Painting n frame'' painting'' restrFrames' E'
    restrPainting' cohFrames p d (Hp := Hp) (E := E);
  restrPainting {E'} p q {Hpq: p <= q} {Hq: q <= n.+1} ε {E} {d: frame p}:
    painting p d -> painting' p (restrFrame p q ε d) :=
    RestrPainting n frame'' painting'' restrFrames' E' restrPainting'
    cohFrames p q ε (Hp := Hp) (Hpq := Hpq) (Hq := Hq) (E := E) d;
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

Class νType := {
  prefix'': Type;
  data: prefix'' -> νTypeAux;
}.

(***************************************************)
(** The construction of [νType n+1] from [νType n] *)

(** Extending the initial prefix *)
Definition mkPrefix'' {C: νType}: Type :=
  { D: C.(prefix'') &T
    mkFrameOfRestrFrames' (n := O) (C.(data) D).(restrFrames') -> HSet }.

Section νTypeData.
Variable C: νType.
Variable D: mkPrefix''.

Definition mkPrev: PrevLevel :=
  mkLevel (C.(data) D.1).(restrFrames') TopPrev (TopRestrFrames D.2).

Definition mkRestrFrames': mkRestrFrameTypes' :=
  mkRestrFramesFrom (C.(data) D.1).(restrFrames') TopPrev (TopRestrFrames D.2)
  ((C.(data) D.1).(cohFrames) D.2).

End νTypeData.

#[local]
Instance mkνType {C: νType}: νType.
  unshelve esplit.
  now exact mkPrefix''.
  unshelve esplit.
  now eapply mkPrev.
  now apply mkRestrFrames'.
  admit.
  admit.
Admitted.
