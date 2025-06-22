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
| EmptyPrev : PrevLevel
| AddPrev (Frame: HSet) (Painting: Frame -> HSet) (rest: PrevLevel) : PrevLevel.

Class RestrFrameTypeBlock := {
  RestrFrameTypesDef: Type;
  FrameDef: RestrFrameTypesDef -> HSet;
}.

Inductive PrevExtension {Prev} : nat -> Type :=
| TopPrev: PrevExtension O
| AddExtraPrev {n: nat} {Frame: HSet} {Painting: Frame -> HSet}:
   PrevExtension (Prev := AddPrev Frame Painting Prev) n ->
   PrevExtension n.+1.

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
Fixpoint mkRestrFrameTypesAndFrames' {Prev}: nat -> RestrFrameTypeBlock :=
  match Prev with
  | EmptyPrev => fun n =>
    {|
      RestrFrameTypesDef := unit;
      FrameDef _ := hunit
    |}
  | AddPrev FramePrev PaintingPrev rest => fun n =>
    {|
      RestrFrameTypesDef :=
        { R: (mkRestrFrameTypesAndFrames' n.+1).(RestrFrameTypesDef) &T
          forall q (Hq: q <= n) (ε: arity),
          (mkRestrFrameTypesAndFrames' n.+1).(FrameDef) R -> FramePrev };
      FrameDef R :=
        { d: (mkRestrFrameTypesAndFrames' (Prev := rest) n.+1).(FrameDef) R.1 &
          hforall ε, PaintingPrev (R.2 O leY_O ε d) }
    |}
  end.

Definition mkRestrFrameTypes' Prev n :=
  (mkRestrFrameTypesAndFrames' (Prev := Prev) n).(RestrFrameTypesDef).

Definition mkFrameOfRestrFrames' Prev n: mkRestrFrameTypes' Prev n -> HSet :=
  (mkRestrFrameTypesAndFrames' (Prev := Prev) n).(FrameDef).

Inductive RestrFramesExtension {Prev}: forall n
  (restrs : mkRestrFrameTypes' Prev n), PrevExtension n -> Type :=
| TopRestrFrames restrs':
  forall E: mkFrameOfRestrFrames' Prev O restrs' -> HSet,
  RestrFramesExtension O restrs' TopPrev
| AddExtraRestrFrame n FramePrev PaintingPrev extraPrev restrs':
  forall restr': forall q (Hq: q <= n) (ε: arity),
          mkFrameOfRestrFrames' Prev n.+1 restrs' -> FramePrev.(Dom),
  RestrFramesExtension (Prev := AddPrev FramePrev PaintingPrev Prev) n
    (restrs'; restr') extraPrev ->
    RestrFramesExtension n.+1 restrs' (AddExtraPrev (Prev := Prev) extraPrev).

(* Example: if Prev := EmptyPrev, extraPrev := [], extraRestrs' := ([],E)
   mkPainting:= [E] *)

Fixpoint mkPainting' {Prev} n (restrs': mkRestrFrameTypes' Prev n)
  extraPrev (extraRestrs' : RestrFramesExtension n restrs' extraPrev):
  mkFrameOfRestrFrames' Prev n restrs' -> HSet :=
  match extraRestrs' in RestrFramesExtension n restrs' extraPrev
     return mkFrameOfRestrFrames' Prev n restrs' -> HSet
  with
  | TopRestrFrames _ E => fun d => E d
  | AddExtraRestrFrame n FramePrev PaintingPrev extraPrev restrs' restr' extraRestrs' => fun d =>
       {l: hforall ε, PaintingPrev (restr' O leY_O ε d) &
        mkPainting' (Prev := AddPrev FramePrev PaintingPrev Prev) n (restrs'; restr') extraPrev extraRestrs' (d; l)}
  end.

Definition MatchPrev
  (loop: forall Prev n (restrs': mkRestrFrameTypes' Prev n)
  extraPrev (extraRestrs': RestrFramesExtension n restrs' extraPrev), PrevLevel)
  {Prev} :=
  match Prev return forall n (restrs': mkRestrFrameTypes' Prev n)
  extraPrev (extraRestrs': RestrFramesExtension n restrs' extraPrev), PrevLevel
   with
   | EmptyPrev => fun _ _ _ _ => EmptyPrev
   | AddPrev FramePrev PaintingPrev Prev => fun n restrs' extraPrev extraRestrs' =>
    loop Prev n.+1 restrs'.1
        (AddExtraPrev extraPrev)
        (AddExtraRestrFrame n FramePrev PaintingPrev extraPrev restrs'.1 restrs'.2 extraRestrs')
   end.

Fixpoint mkLevelRec Prev n (restrs': mkRestrFrameTypes' Prev n)
  extraPrev (extraRestrs': RestrFramesExtension n restrs' extraPrev):
  PrevLevel :=
  AddPrev (mkFrameOfRestrFrames' Prev n restrs')
    (mkPainting' n restrs' extraPrev extraRestrs')
    (MatchPrev mkLevelRec n restrs' extraPrev extraRestrs').

(* Example: if Prev := EmptyPrev, extraPrev := [], extraRestrs' := ([],E)
   mkLevel := [{frame:=unit;painting:=E}] *)

Definition mkLevel {Prev} n (restrs': mkRestrFrameTypes' Prev n)
  extraPrev (extraRestrs': RestrFramesExtension n restrs' extraPrev):
  PrevLevel :=
  AddPrev (mkFrameOfRestrFrames' Prev n restrs')
    (mkPainting' n restrs' extraPrev extraRestrs')
    (MatchPrev mkLevelRec n restrs' extraPrev extraRestrs').

(* Example: if Prev := EmptyPrev, extraPrev := [], extraRestrs' := ([],E)
   mkRestrFrameTypes := [unit -> unit] *)

Definition mkRestrFrameTypes {Prev} n restrs' extraPrev
  extraRestrs' :=
  (mkRestrFrameTypesAndFrames'
    (Prev := mkLevel (Prev := Prev) n restrs' extraPrev
      extraRestrs') n).(RestrFrameTypesDef).

Definition mkPrevRestrFrameTypes {Prev} n restrs' extraPrev extraRestrs' :=
  (mkRestrFrameTypesAndFrames'
    (Prev := MatchPrev mkLevelRec (Prev := Prev) n restrs' extraPrev
      extraRestrs') n.+1).(RestrFrameTypesDef).

(* Example: if Prev := EmptyPrev, extraPrev := [], extraRestrs' := ([],E)
   mkFrameOfRestrFrames [restr: unit -> unt] := [unit; \().∀ω.E(restr())]
      (presented as a Sigma-type, i.e. {d:unit & ∀ω.E(restr())} *)

Definition mkFrameOfRestrFrames {Prev} n restrs' extraPrev extraRestrs'
  : mkRestrFrameTypes (Prev := Prev) n restrs' extraPrev extraRestrs' -> HSet :=
    mkFrameOfRestrFrames' (mkLevel n restrs' extraPrev extraRestrs') n.

Definition mkPrevFrameOfRestrFrames {Prev} n {restrs' extraPrev extraRestrs'}:
  mkPrevRestrFrameTypes (Prev := Prev) n restrs' extraPrev
    extraRestrs' -> HSet :=
  mkFrameOfRestrFrames'
    (MatchPrev mkLevelRec n restrs' extraPrev extraRestrs') n.+1.

(* Examples *)
Check fun E restr => eq_refl:
  (mkFrameOfRestrFrames'
      (AddPrev hunit (fun d : hunit => E d) EmptyPrev) 0 restr).(Dom) =
  {a : unit &T forall a0 : arity, E (restr.2 0 leY_O a0 a)}.
Check fun E' restr E => eq_refl:
  mkPainting' (Prev := AddPrev hunit (fun d => E' d) EmptyPrev) O
  restr TopPrev (TopRestrFrames _ E)
  = fun (d : {a : unit &T forall a0 : arity, E' (restr.2 0 leY_O a0 a)}) => E d.
Check eq_refl : mkRestrFrameTypes' EmptyPrev 0 = unit.
Check eq_refl : mkRestrFrameTypes (Prev := EmptyPrev) 0 tt
  TopPrev (TopRestrFrames _ _) =
                       {_ : unit &T forall q : nat, q <= 0 -> arity -> unit -> unit}.
Check fun E' restr E => eq_refl :
  mkRestrFrameTypes (Prev := AddPrev hunit (fun d => E' d) EmptyPrev) 0
  restr TopPrev (TopRestrFrames _ E)
  = {R : {_ : unit &T forall q : nat, q <= 1 -> arity -> unit -> unit} &T
      forall q : nat, q <= 0 -> arity ->
       {a : unit &T forall a0 : arity, {a1 : forall a1 : arity, E' (restr.2 0 leY_O a1 (R.2 0 leY_O a0 a)) &T E (R.2 0 leY_O a0 a; a1)}} ->
       {a : unit &T forall a0 : arity, E' (restr.2 0 leY_O a0 a)}}.

Class CohFrameTypeBlock {Prev n restrs extraPrev extraRestrs} := {
  CohFrameTypesDef: Type;
  RestrFramesDef: CohFrameTypesDef ->
    mkRestrFrameTypes (Prev := Prev) n restrs extraPrev extraRestrs
}.

Variable RestrPainting':
  forall {Prev n} {FramePrev: HSet} {PaintingPrev: FramePrev -> HSet}
    {restrFrames': mkRestrFrameTypes' (AddPrev FramePrev PaintingPrev Prev) n}
    {extraPrev: PrevExtension (Prev := AddPrev FramePrev PaintingPrev Prev) n}
    {extraRestrs': RestrFramesExtension n.+1 restrFrames'.1
      (AddExtraPrev extraPrev)}
    q (Hq: q <= n) ε
    (d: mkFrameOfRestrFrames' Prev n.+1 restrFrames'.1),
  mkPainting' n.+1 restrFrames'.1 (AddExtraPrev extraPrev) extraRestrs' d ->
  PaintingPrev (restrFrames'.2 q Hq ε d).

Theorem coerce {Prev n restrFrames' extraPrev extraRestrs}:
  mkLevel n restrFrames' extraPrev extraRestrs =
  mkLevelRec Prev n restrFrames' extraPrev extraRestrs.
Proof.
destruct Prev.
- reflexivity.
- simpl. unfold mkLevel. intros. f_equal.
Defined.

Fixpoint mkCohFrameTypesAndRestrFrames {Prev}:
  forall n (restrFrames' : mkRestrFrameTypes' Prev n)
    extraPrev
    (extraRestrs': RestrFramesExtension n restrFrames' extraPrev),
    CohFrameTypeBlock :=
  match Prev return forall n (restrFrames' : mkRestrFrameTypes' Prev n)
    extraPrev
    (extraRestrs': RestrFramesExtension n restrFrames' extraPrev),
    CohFrameTypeBlock
  with
  | EmptyPrev =>
    fun n restrFrames' extraPrev extraRestrs' =>
    {|
      CohFrameTypesDef := unit;
      RestrFramesDef _ := (tt; fun _ _ _ _ => tt):
        mkRestrFrameTypes (Prev := EmptyPrev) n restrFrames'
        extraPrev extraRestrs'
    |}
  | AddPrev FramePrev PaintingPrev Prev =>
    fun n restrFrames' extraPrev extraRestrs' =>
    let restrFrames := (mkCohFrameTypesAndRestrFrames n.+1 restrFrames'.1 (AddExtraPrev extraPrev) (AddExtraRestrFrame _ _ _ _ _ restrFrames'.2 extraRestrs')).(RestrFramesDef) in
    let cohFrameTypes := (mkCohFrameTypesAndRestrFrames n.+1 restrFrames'.1 (AddExtraPrev extraPrev) (AddExtraRestrFrame _ _ _ _ _ restrFrames'.2 extraRestrs')).(CohFrameTypesDef) in
    {|
      CohFrameTypesDef := { Q:
        cohFrameTypes &T
        (* statement of cohFrameType(n+2,p) *)
        let restrFrame := (restrFrames Q).2 in
        forall r q (Hrq: r <= q) (Hq: q <= n) (ε ω: arity) d,
        restrFrames'.2 q Hq ε ((restrFrames Q).2 r (leY_trans Hrq (leY_up Hq)) ω d) =
        restrFrames'.2 r (leY_trans Hrq ( Hq)) ω ((restrFrames Q).2 q.+1 (⇑ Hq) ε d) };
      RestrFramesDef Q :=
      (* RestrFrame(n+2,p+1) *)
      let restrFrame q (Hq: q <= n) ε
        (d: mkFrameOfRestrFrames _ _ _ _ _) :=
        ((restrFrames Q.1).2 q.+1 (⇑ Hq) ε d.1 as rf in _;
        fun ω => rew [PaintingPrev] Q.2 O q leY_O Hq ε ω d.1 in
          RestrPainting' q Hq ε _ (d.2 ω)
          in forall ω, PaintingPrev (restrFrames'.2  _ _ _ rf))
      in rew [ fun L => {R &T forall ω : nat, ω <= n -> arity ->
                   (mkRestrFrameTypesAndFrames' (Prev := L) n.+1).(@FrameDef) R -> _} ] coerce in
          (restrFrames Q.1 as rf in _;
           restrFrame in forall q Hq ω, (mkFrameOfRestrFrames _ _ _ _ rf) -> _)
          : mkRestrFrameTypes (Prev := AddPrev FramePrev PaintingPrev Prev)
            n restrFrames' extraPrev extraRestrs'
    |}
  end.

(* Example: if Prev := EmptyPrev, extraPrev := [], extraRestrs' := ([],E)
   mkCohFrameTypes := [] *)

Definition mkCohFrameTypes {Prev n} restrFrames' extraPrev extraRestrs' :=
  (mkCohFrameTypesAndRestrFrames (Prev := Prev) n restrFrames' extraPrev extraRestrs').(CohFrameTypesDef).

(* Example: if Prev := EmptyPrev, extraPrev := [], extraRestrs' := ([],E)
   mkRestrFramesFrom := [] *)

Definition mkRestrFramesFrom {Prev n} restrFrames' extraPrev extraRestrs' :=
  (mkCohFrameTypesAndRestrFrames (Prev := Prev) n restrFrames' extraPrev extraRestrs').(RestrFramesDef).

Definition mkPrevRestrFramesFrom {Prev n} restrFrames' extraPrev
  extraRestrs' cohs :=
  (mkRestrFramesFrom (Prev := Prev) (n := n) restrFrames' extraPrev extraRestrs' cohs).1.

(* Example: if Prev := EmptyPrev, extraPrev := [], extraRestrs' := ([],E) cohs=[]
   then mkLevel := [{frame:=unit;painting:=E}] and
   mkRestrFrameFrom := [\qω().()]
      (presented as a dependent pair, i.e. ((),\qω().()) *)

Definition mkRestrFrameFrom {Prev n restrFrames' extraPrev extraRestrs' cohs}:
  forall q (Hq: q <= n) ε,
    mkPrevFrameOfRestrFrames n
      (mkPrevRestrFramesFrom restrFrames' extraPrev extraRestrs' cohs) ->
    mkFrameOfRestrFrames' Prev n restrFrames' :=
   ((mkCohFrameTypesAndRestrFrames n restrFrames' extraPrev extraRestrs').(RestrFramesDef) cohs).2.

Inductive CohFramesExtension {Prev}: forall n
  (restrs': mkRestrFrameTypes' Prev n)
  (extraPrev: PrevExtension n)
  (extraRestrs': RestrFramesExtension n restrs' extraPrev),
  mkCohFrameTypes restrs' extraPrev extraRestrs' -> Type :=
| TopCoh
    restrs'
    (E: mkFrameOfRestrFrames' Prev O restrs' -> HSet)
    (cohs: mkCohFrameTypes restrs' TopPrev (TopRestrFrames restrs' E))
    : CohFramesExtension O restrs' TopPrev (TopRestrFrames restrs' E) cohs
| AddCohFrame n FramePrev PaintingPrev
    (extraPrev: PrevExtension (Prev := AddPrev FramePrev PaintingPrev Prev) n)
    (restrs': mkRestrFrameTypes' Prev n.+1)
    (restr': forall q (Hq: q <= n) (ε: arity),
          mkFrameOfRestrFrames' Prev n.+1 restrs' -> FramePrev.(Dom))
    (extraRestrs': RestrFramesExtension
      (Prev := AddPrev FramePrev PaintingPrev Prev) n
      (restrs'; restr') extraPrev)
    cohs:
    let restrFrames cohs :=
       mkRestrFramesFrom (n := n.+1) restrs' (AddExtraPrev extraPrev)
        (AddExtraRestrFrame _ _ _ _ _ restr' extraRestrs')
       cohs: mkRestrFrameTypes n.+1 restrs' (AddExtraPrev extraPrev)    (AddExtraRestrFrame _ _ _ _ _ restr' extraRestrs') in
   let restrFrame cohs := (restrFrames cohs).2 in
   forall coh: forall r q (Hrq: r <= q) (Hq: q <= n) (ε ω: arity) d,
          restr' q Hq ε (restrFrame cohs r (leY_trans Hrq (leY_up Hq)) ω d)
          = restr' r (leY_trans Hrq ( Hq)) ω (restrFrame cohs q.+1 (⇑ Hq) ε d),
  CohFramesExtension (Prev := AddPrev FramePrev PaintingPrev Prev) n (restrs'; restr') extraPrev
    extraRestrs' (cohs as cs in _ ; coh in forall r q Hrq Hq ε ω d, restr' q Hq ε (restrFrame cs r _ _ d) = _) ->
  CohFramesExtension n.+1 restrs'
    (AddExtraPrev extraPrev)
    (AddExtraRestrFrame n FramePrev PaintingPrev extraPrev restrs' restr' extraRestrs')
    cohs.

Definition mkExtension {Prev n} {restrs' : mkRestrFrameTypes' Prev n}
    {extraPrev} {extraRestrs' : RestrFramesExtension n restrs' extraPrev}:
    PrevExtension (Prev := mkLevel n restrs' extraPrev extraRestrs') n.
induction extraRestrs'.
- constructor.
- econstructor. rewrite coerce. eapply IHextraRestrs'.
Defined.

Definition mkRestrFramesExtension {Prev n}
    {restrs' : mkRestrFrameTypes' Prev n}
    {extraPrev : PrevExtension n} {extraRestrs' cohs}:
    RestrFramesExtension (Prev := mkLevel n restrs' extraPrev extraRestrs') n
       (mkRestrFramesFrom restrs' extraPrev extraRestrs' cohs)
       mkExtension.
induction extraRestrs'.
- constructor.
Admitted.

Definition mkPainting {Prev n restrs' extraPrev extraRestrs' cohs} :=
  mkPainting' (Prev := mkLevel n restrs' extraPrev extraRestrs') n
    (mkRestrFramesFrom restrs' extraPrev extraRestrs' cohs)
    mkExtension mkRestrFramesExtension:
  mkFrameOfRestrFrames (Prev := Prev) n restrs' extraPrev extraRestrs' _ ->
    HSet.

Definition mkPrevPainting {Prev n restrs' extraPrev extraRestrs' cohs}:
  mkPrevFrameOfRestrFrames (Prev := Prev) n
         (mkPrevRestrFramesFrom restrs' extraPrev extraRestrs' cohs) -> HSet.
eapply mkPainting'.
Admitted.

Definition RestrPainting {Prev n restrs' extraPrev extraRestrs' cohs}
  q (Hq: q <= n) ε d:
  mkPrevPainting d ->
  mkPainting' (Prev := Prev) n restrs' extraPrev extraRestrs'
  (mkRestrFrameFrom (extraPrev := extraPrev)
    (extraRestrs' := extraRestrs') (cohs := cohs) q Hq ε d).
Admitted.

Class νTypeAux n := {
  Prev : PrevLevel;
  restrFrames': mkRestrFrameTypes' Prev n;
  Level := mkLevel Prev restrFrames' TopPrev Top;
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
