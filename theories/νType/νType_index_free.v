Require Import List.
Import Logic.EqNotations ListNotations.
Require Import Logic.FunctionalExtensionality.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT Notation RewLemmas HSet LeInductive.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Remove Printing Let sigT.
Remove Printing Let prod.

Section νType.
Variable arity: HSet.

Section RestrFramesDef.

Inductive PrevLevel :=
| EmptyPrev : PrevLevel
| AddPrev (Frame: HSet) (Painting: Frame -> HSet) (rest: PrevLevel) : PrevLevel.

Class RestrFrameTypeBlock := {
  RestrFrameTypesDef: Type;
  FrameDef: RestrFrameTypesDef -> HSet;
}.

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
*)
Fixpoint mkRestrFrameTypesAndFrames' (Prev : PrevLevel) : RestrFrameTypeBlock :=
  match Prev with
  | EmptyPrev =>
    {|
      RestrFrameTypesDef := unit;
      FrameDef _ := hunit
    |}
  | AddPrev FramePrev PaintingPrev rest =>
    {|
      RestrFrameTypesDef :=
        { R: (mkRestrFrameTypesAndFrames' rest).(RestrFrameTypesDef) &T
          forall q (ε: arity),
          (mkRestrFrameTypesAndFrames' rest).(FrameDef) R -> FramePrev };
      FrameDef R :=
        { d: (mkRestrFrameTypesAndFrames' rest).(FrameDef) R.1 &
          hforall ε, PaintingPrev (R.2 0 ε d) }
    |}
  end.

Definition mkRestrFrameTypes' Prev :=
  (mkRestrFrameTypesAndFrames' Prev).(RestrFrameTypesDef).

Definition mkFrameOfRestrFrames' Prev: mkRestrFrameTypes' Prev -> HSet :=
  (mkRestrFrameTypesAndFrames' Prev).(FrameDef).

Inductive PrevExtension (Prev: PrevLevel):  Type :=
| TopPrev : PrevExtension Prev
| AddExtraPrev (Frame: HSet) (Painting: Frame -> HSet):
   PrevExtension (AddPrev Frame Painting Prev) ->
   PrevExtension Prev.

Inductive RestrFramesExtension Prev (restrs : mkRestrFrameTypes' Prev): PrevExtension Prev -> Type :=
| Top :
  forall E: mkFrameOfRestrFrames' Prev restrs -> HSet,
  RestrFramesExtension Prev restrs (TopPrev Prev)
| AddRestrFrame FramePrev PaintingPrev extraPrev :
  forall restr: forall q (ε: arity),
          mkFrameOfRestrFrames' Prev restrs -> FramePrev.(Dom),
  RestrFramesExtension (AddPrev FramePrev PaintingPrev Prev) (restrs; restr) extraPrev ->
  RestrFramesExtension Prev restrs (AddExtraPrev Prev FramePrev PaintingPrev extraPrev).

Fixpoint mkPainting' Prev (restrs': mkRestrFrameTypes' Prev)
  extraPrev (extrarestrs' : RestrFramesExtension Prev restrs' extraPrev) :
  mkFrameOfRestrFrames' Prev restrs' -> HSet :=
  match extrarestrs' in RestrFramesExtension _ _ extraPrev
     return mkFrameOfRestrFrames' Prev restrs' -> HSet
  with
  | Top _ _ E => E
  | AddRestrFrame _ _ FramePrev PaintingPrev extraPrev restr' extrarestrs' => fun d =>
       {l: hforall ε, PaintingPrev (restr' 0 ε d) &
        mkPainting' (AddPrev FramePrev PaintingPrev Prev) (restrs'; restr') extraPrev extrarestrs' (d; l)}
  end.

Fixpoint mkLevel (Prev : PrevLevel):
  forall (restrs : mkRestrFrameTypes' Prev)
    extraPrev (extraRestrs : RestrFramesExtension Prev restrs extraPrev),
    PrevLevel :=
  match Prev return forall (restrs : mkRestrFrameTypes' Prev)
    extraPrev (extraRestrs : RestrFramesExtension Prev restrs extraPrev),
    PrevLevel
  with
  | EmptyPrev => fun _ _ _ => AddPrev hunit (fun _ => hunit) EmptyPrev
  | AddPrev FramePrev PaintingPrev Prev => fun restrs extraPrev extraRestrs =>
    AddPrev (mkFrameOfRestrFrames' Prev restrs.1)
        (mkPainting' Prev restrs.1
           (AddExtraPrev _ FramePrev PaintingPrev extraPrev)
            (AddRestrFrame _ _ FramePrev PaintingPrev extraPrev restrs.2 extraRestrs))
        (mkLevel Prev restrs.1
            (AddExtraPrev _ FramePrev PaintingPrev extraPrev)
            (AddRestrFrame _ _ FramePrev PaintingPrev extraPrev restrs.2 extraRestrs))
  end.

Definition mkRestrFrameTypes Prev restrs extraPrev extraRestrs :=
  (mkRestrFrameTypesAndFrames' (mkLevel Prev restrs extraPrev extraRestrs)).(RestrFrameTypesDef).

Definition mkFrameOfRestrFrames Prev restrs extraPrev extraRestrs
  : mkRestrFrameTypes Prev restrs extraPrev extraRestrs -> HSet :=
  (mkRestrFrameTypesAndFrames' (mkLevel Prev restrs extraPrev extraRestrs)).(FrameDef).

Class CohFrameTypeBlock Prev restrs extraPrev extraRestrs := {
  CohFrameTypesDef: Type;
  RestrFramesDef: CohFrameTypesDef -> mkRestrFrameTypes Prev restrs extraPrev extraRestrs
}.

Variable RestrPainting':
  forall Prev restrs' FramePrev PaintingPrev
    (restr': nat -> arity -> mkFrameOfRestrFrames' Prev restrs' -> FramePrev)
    extraPrev extraRestrs' q
    ε (d: mkFrameOfRestrFrames' Prev restrs'),
  mkPainting' Prev restrs' extraPrev extraRestrs' d ->
  PaintingPrev (restr' q ε d).

Fixpoint mkCohFrameTypesAndRestrFrames Prev :=
  match Prev return forall (restrFrames' : mkRestrFrameTypes' Prev)
    extraPrev (extraRestrs : RestrFramesExtension Prev restrFrames' extraPrev),
    CohFrameTypeBlock Prev restrFrames' extraPrev extraRestrs
  with
  | EmptyLevel => fun _ _ _ =>
    {|
      CohFrameTypesDef := unit;
      RestrFramesDef _ := (tt; fun _ _ _ _ _ => tt)
    |}
  | AddPrev _ _ _  => fun restrFrames' _ _ =>
    {|
      CohFrameTypesDef := { Q:
        (mkCohFrameTypesAndRestrFrames restrFrames'.1).(CohFrameTypesDef) &T
        (* statement of cohFrameType(n+2,p) *)
        forall r q (ε ω: arity) d,
        restrFrames'.2 q ε
          (((mkCohFrameTypesAndRestrFrames restrFrames'.1).(RestrFramesDef) Q).2 r  ω d) =
        restrFrames'.2 r ω
            (((mkCohFrameTypesAndRestrFrames p _).(RestrFramesDef) Q).2 q.+1 Hq ε d) };
      RestrFramesDef Q :=
      (* RestrFrame(n+2,p+1) *)
      let restrFrame q := match q with
      | O => fun _ _ _ =>
        False_rect _ (leI_O_contra Hpq)
      | S q => fun ε
        (d: FrameOfRestrFrames p.+1 _) =>
        (((mkCohFrameTypesAndRestrFrames p _).(RestrFramesDef) Q.1).2
          q.+1 _ _ ε d.1 as rf in _;
        fun ω => rew [Painting'' p] Q.2 p q
          ε ω d.1 in RestrPainting' p q ε _ (d.2 ω)
          in forall ω, Painting'' p (RestrFrameFromFull'  _ _ _ rf))
      end in ((mkCohFrameTypesAndRestrFrames p _).(RestrFramesDef) Q.1;
        restrFrame)
    |}
  end.

Class νTypeAux n := {
  Prev : PrevLevel;
  restrFrames': mkRestrFrameTypes'  Prev;
  Level := mkLevel Pref restrFrames' TopPrev Top;
  restrFrame' p {Hp: p.+1 <~ n.+1} q {Hpq Hq} ε (d: frame' p): frame'' p :=
    RestrFrameFromFull'  n frame'' painting'' restrFrames' p
    (Hp := Hp) q (Hpq := Hpq) (Hq := Hq) ε d;
  restrPainting' {E'} p {Hp: p.+1 <~ n.+1} q {Hpq: p <~ q} {Hq: q <~ n} ε
    {d: frame' p}:
    painting' (Hp := leI_down Hp) p d ->
    painting'' p (restrFrame' p q ε (Hpq := Hpq) (Hq := Hq) d);
  cohFrames {E'}:
    mkFullCohFrameTypes n frame'' painting'' restrFrames' E' restrPainting';
  restrFrames {E'}: mkFullRestrFrameTypes n.+1 frame' painting' :=
    mkFullRestrFrames n frame'' painting'' restrFrames' E' restrPainting'
    cohFrames;
  frame {E'} p {Hp: p <~ n.+2}: HSet :=
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
  restrPainting {E'} p {Hp: p.+1 <~ n.+2} q {Hpq: p <~ q} {Hq: q <~ n.+1}
    ε {E} {d: frame p}:
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
}.
