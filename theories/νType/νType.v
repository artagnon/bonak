(** An "indexed" construction of ν-parametric sets
    For ν=1, this builds augmented semi-simplicial sets
    For ν=2, this builds semi-cubical sets *)

Import Logic.EqNotations.
Require Import Logic.FunctionalExtensionality.
From Bonak Require Import Notation.
From Bonak Require Import RewLemmas.

(* Note: this import overrides { & } notation and introduces hforall *)
Set Warnings "-notation-overridden".
From Bonak Require Import HSet.

From Bonak Require Import LeYoneda.
From Bonak Require Import LeInductive.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.
Remove Printing Let sigT.
Remove Printing Let prod.

(** The universe where the ν-parametric sets live *)
Universe m.

(** The universe where the type of ν-parametric sets live *)
Universe m'.

Section νType.
(** The arity [ν] of parametric sets *)
Variable arity: HSet.

(**********************************************)
(** A ν-parametric set is a family of sets obtained by iterating
    Reynolds' parametricity translation.

    For ν=1: this is a collection of colors, of points depending on a
    color, of lines connecting two points of the same color, of
    triangles filling a frame made of three connected lines, of
    tetrahedra filling a frame made of four glued triangles, etc.
    Intuitively, this is:
      X₀ : hSet                                                                colors
      X₁ : X₀ → hSet                                                           points
      X₂ : Πx₀:X₀. X₁x₀ × X₁x₀ → hSet                                          lines
      X₃ : Πx₀:X₀. Πy₀y₁y₂:X₁x₀. X₂x₀(y₀,y₁) × X₂x₀(y₀,y₂) × X₂x₀(y₁y₂) → hSet triangles
    ...
    Formally, following the recursive recipe defined in the file,
    this is equivalently defined as:
      X₀ : unit → hSet                                                  colors
      X₁ : Σ⋆:unit.X₀⋆ → hSet                                           points
      X₂ : Σx₁:(Σx₀:(Σ⋆:unit.X₀⋆).X₁x₀).X₁(x₁.1) → hSet                 lines
      X₃ : Σx₂':(Σx₂:(Σx₁':(Σx₁:(Σx₀:(Σ⋆:unit.X₀⋆).X₁x₀).X₁(x₁.1)).X₂(x₁')).
                 Σx₁:X₁(x₂.1.1).X₂(x₂.1,x₁)).
           X₂((x₂'.1.1.1.1,x₂'.1.1.2),x₂'.2.1) → hSet                   triangles

      where each Xₙ has generically a type Xₙ : frameₙₙ(X₀,...,Xₙ₋₁) → hSet

      Above, frameₙₙ has type pspₙ → hSet, where psp, standing for
      "parametric set prefix", represents an initial sequence
      X₀,...,Xₙ₋₁ of parametric sets.

      Also, arguments of each Xᵢ in a frame are computed from
      previous arguments using "restrictions". These restrictions
      themselves obey coherence rules.

    For ν=2: this is a collection of points, of lines connecting two
    points, of squares filling a frame made of four lines, of cubes
    filling a frame made of six squares, etc.
    Intuitively, this is:
      X₀ : hSet                                                                points
      X₁ : X₀×X₀ → hSet                                                        lines
      X₂ : Πx₀₀x₀₁x₁₀x₁₁:X₀. X₁x₀₀x₁₀ × X₁x₁₀x₁₁ × X₁x₀₀x₀₁ × X₁x₁₀x₁₁ → hSet  squares

    Formally, it is built on a variant of frame that takes 2 copies of each X instead of 1.

    The construction mutually builds the type of frames, frame
    restrictions and coherence conditions on frame restrictions.
*)

Section RestrFramesGenDef.
(* Assume what is needed to build restrFrameType and Frame(restrFrames)
   at level n.+1 for respectively p < n and p <=  n.
   In particular, n is here the level where live FramePrev and PaintingPrev. *)
Variable n: nat.
Variable FramePrev: forall p {Hp: p <~ n}, HSet.
Variable PaintingPrev: forall p {Hp: p <~ n}, FramePrev p (Hp := Hp) -> HSet.

Class RestrFrameTypeBlockGen := {
  RestrFrameTypes: Type;
  Frames: RestrFrameTypes -> HSet;
}.

(* Build the list of pairs of the type RestrFrameTypes of restrFrame'_{p-1}
   and of the definition of frame'_p in function of effective RestrFrames' of these types._
   That is, we build for p <= n:
   p = 0 : { restrFrameTypes = unit ; frame0(restrFrames_{0..0-1}) }
   p = 1 : { restrFrameTypes = {_:unit & restrFrameType0 ; frame1(restrFrames_{0..0}) }
   ...
   p     : { restrFrameTypes = {RestrFrameType0 ... restrFrameType_{p-1}} ; frame1(restrFrames_{0..p-1}) }
 *)
Definition RestrFrameTypesFix :=
  fix aux p: forall (Hp: p <~ n.+1), RestrFrameTypeBlockGen :=
  match p with
  | O => fun (Hp: 0 <~ n.+1) =>
    {| RestrFrameTypes := unit; Frames _ := hunit |}
  | S p => fun (Hp: p.+1 <~ n.+1) =>
    {|
      RestrFrameTypes :=
        { R : (aux p _).(RestrFrameTypes) &T
          forall q (Hpq: p.+1 <~ q.+1) (Hq: q.+1 <~ n.+1) (ε: arity),
          (aux p _).(Frames) R -> FramePrev p (Hp := leI_lower_both Hp)};
      Frames R :=
        { d: (aux p (leI_down Hp)).(Frames) R.1 &
          hforall ε, PaintingPrev p (R.2 p (leI_refl _) Hp ε d) }
    |}
  end.

#[local]
Instance mkRestrFrameTypes p {Hp}:
  RestrFrameTypeBlockGen := RestrFrameTypesFix p Hp.

(* Additionally assume that we have restrFrames available up to level n so as
   to build Frame and Painting at level n.+1 for any p <= n. *)
Definition mkFullRestrFrameTypes :=
  (mkRestrFrameTypes n.+1 (Hp := leI_refl _)).(RestrFrameTypes).
Variable RestrFrames: mkFullRestrFrameTypes.

Definition take_head: forall p {Hp: p <~ n.+1},
  (mkRestrFrameTypes p (Hp := Hp)).(RestrFrameTypes) :=
  fix aux p Hp := match Hp with
  | leI_refl _ => RestrFrames
  | @leI_down _ p Hp => (aux p.+1 Hp).1
  end.

Definition take_tail p {Hp: p.+1 <~ n.+1} := (take_head p.+1 (Hp := Hp)).2:
  forall q (Hpq: p.+1 <~ q.+1) (Hq: q.+1 <~ n.+1),
  arity -> (mkRestrFrameTypes p).(Frames) (take_head p.+1).1 -> FramePrev p.

Definition mkFrames := fun p {Hp: p.+1 <~ n.+1} =>
  (mkRestrFrameTypes p).(Frames) (take_head p (Hp := leI_down Hp)).

Definition mkRestrFrames := fun p {Hp} q {Hpq Hq} =>
  take_tail p (Hp := Hp) q Hpq Hq.

Let Frame p {Hp} := mkFrames p (Hp := Hp).
Let RestrFrame p {Hp} q {Hpq Hq} :=
  mkRestrFrames p (Hp := Hp) q (Hpq := Hpq) (Hq := Hq).

Definition PaintingGen p {Hp: p <~ n}
  {E: Frame n -> HSet} := (fix aux p Hp :=
  match Hp in p <~ _ return Frame p (Hp := leI_raise_both Hp) -> HSet with
  | leI_refl _ => E
  | @leI_down _ p Hp => fun d =>
       {l: hforall ε, PaintingPrev p (RestrFrame p p ε d) &
        (aux p.+1 Hp) (d; l)}
  end) p Hp.

End RestrFramesGenDef.

Section CohFramesDef.
(* We build CohFrameType and RestrFrame at level n.+2
   for respectively p <= n and p <= n.+1, assuming:
   - Frame'' and Painting'' for p <= n
   - RestrFrames' for p <= n *)
Variable n: nat.
Variable Frame'': forall p {Hp: p <~ n}, HSet.
Variable Painting'': forall p {Hp: p <~ n}, Frame'' p (Hp := Hp) -> HSet.
Variable RestrFrames': mkFullRestrFrameTypes n Frame'' Painting''.
Let Frame' p {Hp: p <~ n} :=
  mkFrames n Frame'' Painting'' RestrFrames' p (Hp := leI_raise_both Hp).
Let RestrFrame' p {Hp} q {Hpq Hq} :=
  mkRestrFrames n Frame'' Painting'' RestrFrames' p
  (Hp := Hp) q (Hpq := Hpq) (Hq := Hq).
Variable E: Frame' n (Hp := leI_refl _) -> HSet.
Let Painting' p {Hp} := PaintingGen n Frame'' Painting'' RestrFrames' p
  (Hp := Hp) (E := E).

Class CohFrameTypeBlock p {Hp: p.+1 <~ n.+1} := {
  CohFrameType: Type;
  RestrFrames: CohFrameType -> (mkRestrFrameTypes n (Hp := Hp) Frame'
    Painting' p.+1).(RestrFrameTypes);
}.

Variable RestrPainting': forall p q {Hp: p.+1 <~ n.+1} {Hpq: p.+1 <~ q.+1}
  {Hq: q.+1 <~ n.+1} ε (d: Frame' p),
  Painting' p (Hp := leI_lower_both Hp) d ->
  Painting'' p (RestrFrame' p q ε (Hpq := Hpq) (Hq := Hq) d).

(* Build the list of pairs of the type CohFrameTypeGen of restrFrame'_{p-1}
   and of the definition of frame'_p in function of effective RestrFrames' of these types._
   That is, we build for p <= n:
   p = 0 : { cohFrameTypes_{0..0-1} = unit ; restrFrames0(cohFrames_{0..0-1}):restrFrameTypes_{0..0} }
   p = 1 : { cohFrameTypes_{0..1} = {_:unit & cohFrameType0 ; restrFrame1(cohFrames_{0..0}):restrFrameTypes_{0..1} }
   ...
   p     : { cohFrameTypes_{0..p-1} = {cohFrameType0 ... cohFrameType_{p-1}} ; restrFramep(cohFrames_{0..p-1}):restrFrameTypes_{0..p} }
*)
Definition CohFrameTypeBlockFix :=
  fix aux p: forall (Hp: p <~ n), CohFrameTypeBlock p :=
  match p return forall (Hp: p <~ n), CohFrameTypeBlock p with
    | O => fun _ =>
    {|
      CohFrameType := unit;
      RestrFrames _ := (tt; fun _ _ _ _ _ => tt)
        : (mkRestrFrameTypes n Frame' Painting' 1).(RestrFrameTypes)
    |}
    | S p => fun (Hp: p.+1 <~ n) =>
    {|
      CohFrameType := { Q : (aux p _).(CohFrameType) &T
        forall r q (Hpr: p.+2 <~ r.+2) (Hrq: r.+2 <~ q.+2) (Hq: q.+2 <~ n.+1)
          (ε ω: arity) d,
        RestrFrame' p q ε (((aux p _).(RestrFrames) Q).2 r
          (leI_lower_both Hpr) (leI_down (leI_trans Hrq Hq)) ω d) =
        RestrFrame' p r ω (((aux p _).(RestrFrames) Q).2 q.+1
          (leI_down (leI_trans Hpr Hrq)) Hq ε d) };
      RestrFrames Q :=
      let Frame := (mkRestrFrameTypes n Frame' Painting' p.+1).(Frames) _ in
      let restrFrame q := match q with
      | O => fun (Hpq: p.+2 <~ 1) _ _ _ =>
        False_rect _ (leI_O_contra (leI_lower_both Hpq))
      | S q => fun (Hpq: p.+2 <~ q.+2) (Hq: q.+2 <~ n.+1) ε (d: Frame) =>
        (((aux p _).(RestrFrames) Q.1).2 q.+1 _ _ ε d.1;
        fun ω => rew [Painting'' _] Q.2 p q (leI_refl _) Hpq Hq ε ω d.1 in
          RestrPainting' p q ε _ (d.2 ω))
      end in ((aux p _).(RestrFrames) Q.1; restrFrame)
        : (mkRestrFrameTypes n Frame' Painting' p.+2).(RestrFrameTypes)
    |}
  end.
End CohFramesDef.
(*
cannot satisfy constraint
"forall (q : nat) (Hpq : p0.+2 <~ q.+1) (H : q.+1 <~ n.+1)
   (H0 : arity) (H1 : Frame),
 {x : Frame' p0 &T
 forall x0 : arity,
 Painting'' p0
   (RestrFrame' p0 p0 x0
      (((aux p0 ?Hp1@{p0:=p; p:=p0}).(RestrFrames) Q.1).2 q
         (leI_down (leI_trans (leI_refl p0.+2) Hpq)) H H0 H1.1))}" ==
"(fun
    R : ((fix aux (p : nat) : p <~ n.+1 -> RestrFrameTypeBlockGen :=
            match p as p0 return (p0 <~ n.+1 -> RestrFrameTypeBlockGen) with
            | 0 =>
                fun _ : 0 <~ n.+1 =>
                {|
                  RestrFrameTypeGen := unit;
                  FrameGen := fun _ : unit => hunit
                |}
            | p0.+1 =>
                fun Hp : p0.+1 <~ n.+1 =>
                {|
                  RestrFrameTypeGen :=
                    {R : (aux p0 (leI_down Hp)).(RestrFrameTypeGen) &T
                    forall q : nat,
                    p0.+1 <~ q.+1 ->
                    q.+1 <~ n.+1 ->
                    arity -> (aux p0 (leI_down Hp)).(FrameGen) R -> Frame' p0};
                  FrameGen :=
                    fun
                      R : {R : (aux p0 (leI_down Hp)).(RestrFrameTypeGen) &T
                          forall q : nat,
                          p0.+1 <~ q.+1 ->
                          q.+1 <~ n.+1 ->
                          arity ->
                          (aux p0 (leI_down Hp)).(FrameGen) R -> Frame' p0}
                    =>
                    {d : (aux p0 (leI_down Hp)).(FrameGen) R.1 &
                    hforall ε : arity,
                      Painting' p0 (R.2 p0 (leI_refl p0.+1) Hp ε d)}
                |}
            end) p0.+1 (leI_down ?l4601@{p:=p0; Hp:=?Hp1@{p0:=p; p:=p0}}))
        .(RestrFrameTypeGen) =>
  forall q : nat,
  p0.+2 <~ q.+1 ->
  q.+1 <~ n.+1 ->
  arity ->
  ((fix aux (p : nat) : p <~ n.+1 -> RestrFrameTypeBlockGen :=
      match p as p0 return (p0 <~ n.+1 -> RestrFrameTypeBlockGen) with
      | 0 =>
          fun _ : 0 <~ n.+1 =>
          {| RestrFrameTypeGen := unit; FrameGen := fun _ : unit => hunit |}
      | p0.+1 =>
          fun Hp : p0.+1 <~ n.+1 =>
          {|
            RestrFrameTypeGen :=
              {R0 : (aux p0 (leI_down Hp)).(RestrFrameTypeGen) &T
              forall q0 : nat,
              p0.+1 <~ q0.+1 ->
              q0.+1 <~ n.+1 ->
              arity -> (aux p0 (leI_down Hp)).(FrameGen) R0 -> Frame' p0};
            FrameGen :=
              fun
                R0 : {R0 : (aux p0 (leI_down Hp)).(RestrFrameTypeGen) &T
                     forall q0 : nat,
                     p0.+1 <~ q0.+1 ->
                     q0.+1 <~ n.+1 ->
                     arity ->
                     (aux p0 (leI_down Hp)).(FrameGen) R0 -> Frame' p0} =>
              {d : (aux p0 (leI_down Hp)).(FrameGen) R0.1 &
              hforall ε : arity,
                Painting' p0 (R0.2 p0 (leI_refl p0.+1) Hp ε d)}
          |}
      end) p0.+1 (leI_down ?l4601@{p:=p0; Hp:=?Hp1@{p0:=p; p:=p0}}))
  .(FrameGen) R -> Frame' p0.+1)
   ((aux p0 ?Hp1@{p0:=p; p:=p0}).(RestrFrames) Q.1)"
 *)
Class RestrFrameBlock n p (prefix: Type@{m'})
  (Frame': forall p {Hp: p.+1 <= n}, prefix -> HSet) := {
  Frame {Hp: p <= n}: prefix -> HSet;
  RestrFrame q {Hpq: p.+1 <= q.+1} {Hq: q.+1 <= n} (ε: arity) {D}:
    Frame D -> Frame' p D;
}.

Arguments Frame {n} p {prefix Frame'} _ {Hp} D.
Arguments RestrFrame {n} p {prefix Frame'} _ q {Hpq Hq} ε {D} d.

Class LayerAuxType' {n prefix} :=
  LayerAux_t': forall p (Hp: p.+2 <= n) (D: prefix) (frame': HSet)
    (d: frame'), HSet.

Class LayerAuxType {n prefix frame'} :=
  LayerAux_t: forall p (Hp: p.+1 <= n) D
    (restrFrameBlock: RestrFrameBlock n p prefix frame')
    (d: restrFrameBlock.(Frame p) D), HSet.

Definition FrameFix' {n prefix} (layerAux': LayerAuxType') :=
  fix frame' p: forall (Hp: p.+1 <= n) (D: prefix), HSet :=
  match p with
  | O => fun Hp D => hunit
  | S p => fun Hp D => {d: frame' p _ D & layerAux' _ _ D (frame' p _ D) d}
  end.

Arguments FrameFix' {n prefix} layerAux' p {Hp} D.

Class RestrLayerAuxType {n prefix}
  {layerAux': LayerAuxType'}
  {layerAux: LayerAuxType}
  (frame' := fun p {Hp} D => FrameFix' layerAux' p (Hp := Hp) D)
  (layer' := fun {p Hp D} => layerAux' p Hp D (frame' p D)) :=
  RestrLayerAux_t: forall p q (Hpq: p.+2 <= q.+2) (Hq: q.+2 <= n) ε
    (D: prefix) (restrFrameBlock: RestrFrameBlock n p prefix frame')
    (d: restrFrameBlock.(Frame p) D),
    layerAux p _ D restrFrameBlock d ->
      layer' (restrFrameBlock.(RestrFrame p) q.+1 ε d).

Definition RestrFrameBlockFix {n prefix}
  (layerAux': LayerAuxType')
  (frame' := fun p {Hp} D => FrameFix' layerAux' p (Hp := Hp) D)
  (layerAux: LayerAuxType)
  (restrLayerAux: RestrLayerAuxType) :=
  fix restrFrameBlock {p}: RestrFrameBlock n p prefix frame' :=
  match p with
  | O => {| Frame _ _ := hunit; RestrFrame _ _ _ _ _ _ := tt :> hunit |}
  | S p => {|
    Frame Hp D := {d: restrFrameBlock.(Frame p) D & layerAux p Hp D restrFrameBlock d};
    RestrFrame q := match q
    return forall (Hpq: p.+2 <= q.+1) (Hq: q.+1 <= n) _ D, _ -> frame' p.+1 D
    with
    | O => fun Hpq _ _ _ => ltac:(le_contra Hpq)
    | S q => fun Hpq Hq ε D d =>
      (restrFrameBlock.(RestrFrame p) q.+1 ε d.1;
       restrLayerAux p q Hpq Hq ε D restrFrameBlock _ d.2)
    end
  |}
  end.

Arguments RestrFrameBlockFix {n prefix} layerAux' layerAux restrLayerAux {p}.

Class CohFrameBlock n p (prefix: Type@{m'})
  (Frame'': forall p {Hp: p.+2 <= n}, prefix -> HSet)
  (frame': forall p {Hp: p.+1 <= n}, prefix -> HSet)
  (restrFrame' : forall p q {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n} (ε: arity)
    {D: prefix}, frame' p D -> FramePrev p D) := {
  RF: RestrFrameBlock n p prefix frame';
  CohFrame r q {Hpr: p.+2 <= r.+2} {Hrq: r.+2 <= q.+2} {Hq: q.+2 <= n}
    {ε ω} {D} (d: RF.(Frame p) D):
    restrFrame' p q (Hpq := Hpr ↕ Hrq) (Hq := Hq) ε (RF.(RestrFrame p) r ω d) =
    restrFrame' p r ω (Hpq := Hpr) (Hq := Hrq ↕ Hq)
      (RF.(RestrFrame p) q.+1 ε d);
}.

Arguments RF {n p prefix FramePrev frame' restrFrame'} _.
Arguments CohFrame {n p prefix FramePrev frame' restrFrame'} _ r q
  {Hpr Hrq Hq ε ω} {D} d.

(** An ν-parametric type truncated at level [n] consists of:

  - a [prefix] of parametric types up to dimension [n],
  - a type of frames with their restrictions and coherence of
    restrictions [Frame] (depending on their values are dimension [n]-1
    and [n]-2) that are Σ-types of length [n] that is recursively built
    out by induction on some [p] ranging from 0 to [n]
  - a type of paintings (with their restrictions and coherence of
    restrictions) [Painting] (depending on their values [PaintingPrev] at
    dimensions [n]-1 and [n]-2) that are also recursively built out from
    partial paintings
  - axioms characterizing the definition of [Frame] and [Painting] in
    the previous dimensions, so that the induction can be carried
*)

(** The construction maintains at each step of the induction the three
    last levels of frames (called [frame''], [frame'], [frame]), the
    two restrictions between them (called [restrFrame'] and
    [restrFrame]) and the coherence between these two restrictions
    (called [cohFrame]). *)

(** We build paintings using an iterated construction: a painting at level n
    depends on paintings at level n-1 and n-2; just as we have frame' and
     frame'', we have painting' and painting''. *)

Class νType n := {
  prefix: Type@{m'};
  frame'' p {Hp: p.+2 <= n}: prefix -> HSet;
  painting'' {p} {Hp: p.+2 <= n} {D: prefix}: frame'' p D -> HSet;
  restrFrame' p {Hp: p.+2 <= n} {D: prefix}:
    (RestrFrameTypeBlockFix' n prefix frame'' (@painting'') D p).(RestrFrameType');
  frame' p {Hp} D :=
    (RestrFrameTypeBlockFix' n prefix frame'' (@painting'') D p).(Frames) (restrFrame' p);
  painting' {p} {Hp: p.+1 <= n} {D: prefix}: frame' p D -> HSet;
  cohFrameAux {p} r q {Hpr: p.+2 <= r.+2} {Hrq: r.+2 <= q.+2} {Hq: q.+2 <= n}
    {ε ω: arity} {D: prefix}
    (restrFrameBlock: RestrFrameBlock n p prefix frame')
    (d: restrFrameBlock.(Frame p) D):
    restrFrame' p q ε (restrFrameBlock.(RestrFrame p) r ω d) =
    restrFrame' p r ω (restrFrameBlock.(RestrFrame p) q.+1 ε d);
  restrPainting' p q {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n} (ε: arity) {D: prefix}
    {d: frame' p D}: painting' d -> painting'' (restrFrame' p q ε d);
  layerAux {p} {Hp: p.+1 <= n} {D: prefix}
    (restrFrameBlock: RestrFrameBlock n p prefix frame')
    (d: restrFrameBlock.(Frame p) D) :=
    hforall ε, painting' (restrFrameBlock.(RestrFrame p) p ε d);
  restrLayerAux {p q} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n} ε {D: prefix}
    (restrFrameBlock: RestrFrameBlock n p prefix frame')
    {d: restrFrameBlock.(Frame p) D}:
    layerAux restrFrameBlock d ->
    layer' (restrFrameBlock.(RestrFrame p) q.+1 ε d) :=
    fun l ω => rew [painting''] cohFrameAux p q restrFrameBlock d in
      restrPainting' p q ε (l ω);
  restrFrameBlock {p} := RestrFrameBlockFix (@layerAux') (@layerAux)
    (@restrLayerAux) (p := p);
  frame p {Hp : p <= n} (D: prefix) := restrFrameBlock.(Frame p) D;
  restrFrame p q {Hpq: p.+1 <= q.+1} {Hq: q.+1 <= n} ε {D: prefix} d :=
    restrFrameBlock.(RestrFrame p) q ε (D := D) d;
  cohFrame {p} r q {Hpr: p.+2 <= r.+2} {Hrq: r.+2 <= q.+2} {Hq: q.+2 <= n}
    {ε ω: arity} {D: prefix} :=
    cohFrameAux (ε := ε) (ω := ω) (D := D) r q restrFrameBlock;
  layer {p} {Hp: p.+1 <= n} {D} (d: frame p D) := layerAux restrFrameBlock d;
  restrLayer p q {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n} (ε: arity) {D: prefix}
    {d: frame p D} := restrLayerAux (D := D) ε restrFrameBlock (d := d);
  painting {p} {Hp: p <= n} {D} (E: frame n D -> HSet)
    (d: frame p D): HSet :=
    le_induction Hp (fun p Hp => frame p D -> HSet) E
    (fun p Hp (Hind: frame p.+1 D -> HSet) (d: frame p D) =>
      {l: layer d & Hind (d; l)}) d;
  restrPainting p q {Hpq: p.+1 <= q.+1} {Hq: q.+1 <= n} ε {D}
    {E: frame n D -> HSet} {d: frame p D}
    (c: painting E d): painting' (restrFrame p q ε d);
  cohPainting p r q {Hpr: p.+2 <= r.+2} {Hrq: r.+2 <= q.+2} {Hq: q.+2 <= n}
    ε ω {D} (E: frame n D -> HSet) (d: frame p D)
    (c: painting E d):
    rew [painting''] cohFrame r q d in
    restrPainting' p q ε (restrPainting p r ω c) =
      (restrPainting' p r ω (restrPainting p q.+1 ε c));
}.

(* We want ε and ω to be printed, but have them inferred;
   Coq doesn't support this. *)

Arguments prefix {n} _.
Arguments frame'' {n} _ p {Hp} D.
Arguments painting'' {n} _ {p Hp D} d.
Arguments frame' {n} _ p {Hp} D.
Arguments restrFrame' {n} _ p q {Hpq Hq} ε {D} d.
Arguments layer' {n} _ {p Hp D} d.
Arguments painting' {n} _ {p Hp D} d.
Arguments restrPainting' {n} _ p q {Hpq Hq} ε {D} [d] c.
Arguments frame {n} _ p {Hp} D.
Arguments restrFrame {n} _ p q {Hpq Hq} ε {D} d.
Arguments cohFrame {n} _ {p} r q {Hpr Hrq Hq ε ω D}.
Arguments layer {n} _ {p Hp D} d.
Arguments restrLayer {n} _ p q {Hpq Hq} ε {D d} l.
Arguments painting {n} _ {p Hp D} E d.
Arguments restrPainting {n} _ p q {Hpq Hq} ε {D} {E} [d] c.
Arguments cohPainting {n} _ p r q {Hpr Hrq Hq} ε ω {D} E [d] c.

(***************************************************)
(** The construction of [νType n+1] from [νType n] *)

(** Extending the initial prefix *)
Definition mkPrefix {n} {C: νType n}: Type@{m'} :=
  { D : C.(prefix) &_T C.(frame) n D -> HSet }.

(** The coherence conditions that Frame needs to satisfy to build the next level
   of Frame. These will be used in the proof script of mkFrame. *)

Definition mkFrame'' {n} {C: νType n} p {Hp: p.+2 <= n.+1} (D: mkPrefix) :=
  C.(Frames) p D.1.

Definition mkFrame' {n} {C: νType n} p {Hp: p.+1 <= n.+1} (D: mkPrefix) :=
  C.(frame) p D.1.

Definition mkLayer {n} {C: νType n} {p} {Hp: p.+1 <= n.+1}
  {F: RestrFrameBlock n.+1 p mkPrefix mkFrame'} {D} (d: F.(Frame p) D): HSet :=
  hforall ε, C.(painting) D.2 (F.(RestrFrame p) p ε d).

Definition mkLayer' {n} {C: νType n} {p} {Hp: p.+2 <= n.+1} {D: mkPrefix}
  (d: mkFrame' p D): HSet := C.(layer) d.

Definition mkRestrFrameAux' {n} {C: νType n} p q {Hpq: p.+2 <= q.+2}
  {Hq: q.+2 <= n.+1} (ε: arity) {D: mkPrefix} :=
    C.(restrFrame) p q ε (D := D.1).

Definition mkRestrLayer {n} {C: νType n} p q {Hpq: p.+2 <= q.+2}
  {Hq: q.+2 <= n.+1} {ε}
  {CF: CohFrameBlock n.+1 p mkPrefix mkFrame'' mkFrame' mkRestrFrameAux'}
  {D} {d: CF.(RF).(Frame p) D}:
  mkLayer d -> mkLayer' (CF.(RF).(RestrFrame p) q.+1 ε d) :=
  fun l ω => rew [C.(painting')] CF.(CohFrame) p q d in
    C.(restrPainting) p q ε (l ω).

Definition mkCohLayer {n} {C: νType n} {p r q} {Hpr: p.+3 <= r.+3}
  {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1} {ε ω}
  {CF: CohFrameBlock n.+1 p mkPrefix mkFrame'' mkFrame' mkRestrFrameAux'}
  {D} {d: CF.(RF).(Frame p) D} (l: mkLayer d):
  rew [C.(layer')] CF.(CohFrame) r.+1 q.+1 d in
    C.(restrLayer) p q ε (mkRestrLayer p r l) =
    C.(restrLayer) p r ω (mkRestrLayer p q.+1 l).
Proof.
  intros *.
  apply functional_extensionality_dep; intros 𝛉; unfold layer'.
  rewrite <- map_subst_app with
    (P := fun 𝛉 x => C.(painting'') (C.(restrFrame') p p 𝛉 x)).
  unfold restrLayer, mkRestrLayer.
  rewrite <- map_subst with (f := C.(restrPainting') p q ε).
  rewrite <- map_subst with
    (f := C.(restrPainting') p r ω).
  rewrite rew_map with
    (P := fun x => C.(painting'') x)
    (f := fun x => C.(restrFrame') p p 𝛉 x),
  rew_map with
    (P := fun x => C.(painting'') x)
    (f := fun x => C.(restrFrame') p q ε x),
  rew_map with
    (P := fun x => C.(painting'') x)
    (f := fun x => C.(restrFrame') p r ω x).
  rewrite <- (C.(cohPainting) p r q).
  repeat rewrite rew_compose.
  apply rew_swap with (P := fun x => C.(painting'') x).
  rewrite rew_app_rl. now trivial.
  now apply (C.(frame'') p D.1).(UIP).
Qed.

#[local]
Instance mkCohFrameBlock0 {n} {C: νType n}:
  CohFrameBlock n.+1 O mkPrefix mkFrame'' mkFrame' mkRestrFrameAux'.
  unshelve esplit.
  * unshelve esplit.
    - intros. now exact hunit. (* Frame0 *)
    - intros. now exact tt. (* restrFrame0 *)
  * now intros.
Defined.

#[local]
Instance mkCohFrameBlockSp {n} {C: νType n} {p}
  {CF: CohFrameBlock n.+1 p mkPrefix mkFrame'' mkFrame' mkRestrFrameAux'}:
  CohFrameBlock n.+1 p.+1 mkPrefix mkFrame'' mkFrame' mkRestrFrameAux'.
  unshelve esplit.
  * unshelve esplit.
    - intros Hp D. now exact {d : CF.(RF).(Frame p) D & mkLayer d}.
    - simpl; intros * ε * (d, l); invert_le Hpq. (* restrFramep *)
      now exact (CF.(RF).(RestrFrame p) _ ε d; mkRestrLayer p q l).
  * simpl; intros q r Hpr Hrq Hq ε ω D (d, l). (* cohframep *)
    invert_le Hpr; invert_le Hrq.
    now exact (= CF.(CohFrame) q.+1 r.+1 d; mkCohLayer l).
Defined.

(** Finally, we can define mkFrame at level n.+1 for all p *)
#[local]
Instance mkCohFrameBlock {n} {C: νType n} {p}:
  CohFrameBlock n.+1 p mkPrefix mkFrame'' mkFrame' mkRestrFrameAux'.
  induction p.
  * now exact mkCohFrameBlock0. (* p = O *)
  * now exact mkCohFrameBlockSp. (* p = S _ *)
Defined.

(** For [Painting], we take a different strategy. We first define [mkpainting],
    [mkRestrPainting], and lemmas corresponding to their computational properties *)

(** First, memoizing the previous levels of [Painting] *)
Definition mkPainting'' {n} {C: νType n} {p} {Hp: p.+2 <= n.+1} {D: mkPrefix}:
  mkFrame'' p D -> HSet := C.(painting').

(** Then, the component [painting] of [Painting], built by upwards induction from [p] to [n] *)

Definition mkPainting' {n} {C: νType n} {p} {Hp: p <= n.+1}
  {D: mkPrefix} d: HSet := C.(painting) D.2 d.

Definition mkPaintingType n {C: νType n} p {Hp: p <= n.+1} {D: mkPrefix}
  (E: (mkCohFrameBlock).(RF).(Frame n.+1) D -> HSet)
  (d: (mkCohFrameBlock).(RF).(Frame p) D): HSet :=
  le_induction Hp (fun p Hp => mkCohFrameBlock.(RF).(Frame p) D -> HSet) E
  (fun p Hp (Hind: mkCohFrameBlock.(RF).(Frame p.+1) (Hp := Hp) D -> HSet)
    (d: mkCohFrameBlock.(RF).(Frame p) (Hp := ↓ Hp) D) =>
    {l: mkLayer d & Hind (d; l)}) d.

Lemma mkPaintingType_base_computes {n} {C: νType n}
  {D E} {d: (mkCohFrameBlock).(RF).(Frame n.+1) D}:
  mkPaintingType n n.+1 E d = E d.
Proof.
  unfold mkPaintingType; now rewrite le_induction_base_computes.
Qed.

Lemma mkPaintingType_step_computes {n p} {C: νType n} {Hp: p.+1 <= n.+1} {D}
  {E: (mkCohFrameBlock).(RF).(Frame n.+1) D -> HSet} {d}:
  mkPaintingType n p E d =
  {l: mkLayer d & mkPaintingType n p.+1 E (d; l)} :> Type.
Proof.
  unfold mkPaintingType; now rewrite le_induction_step_computes.
Qed.

(** Now, [restrPainting], and the corresponding computational properties. *)

Definition mkRestrPainting {n} {C: νType n} p q {Hpq: p.+1 <= q.+1}
  {Hq: q.+1 <= n.+1} {ε} {D} E (d: (mkCohFrameBlock).(RF).(Frame p) D)
  (c: mkPaintingType n p E d):
  mkPainting' ((mkCohFrameBlock).(RF).(RestrFrame p) q ε d).
Proof.
  revert d c; simpl. apply le_induction' with (Hp := Hpq).
  * intros d c. destruct (rew [id] mkPaintingType_step_computes in c) as (l, _).
    now exact (l ε).
  * clear p Hpq; intros p Hpq mkRestrPaintingSp d c; invert_le Hpq.
    destruct (rew [id] mkPaintingType_step_computes in c) as (l, c'). clear c.
    rewrite C.(eqPaintingSp). apply mkRestrPaintingSp in c'.
    now exact (mkRestrLayer p q l; c').
Defined.

Lemma mkRestrPainting_base_computes {n} {C: νType n} {p} {Hp: p.+1 <= n.+1}
  {ε} {D E} {d: (mkFrame p).(frame p) D} {c}:
  mkRestrPainting p p E d c =
  match (rew [id] mkPaintingType_step_computes in c) with
  | (l; _) => l ε
  end.
Proof.
  unfold mkRestrPainting; now rewrite le_induction'_base_computes.
Qed.

Lemma mkRestrPainting_step_computes {n} {C: νType n} {r q} {Hrq: r.+2 <= q.+2}
  {Hq: q.+2 <= n.+1} {ε} {D E} {d: (mkFrame r).(frame r) D} {c}:
  mkRestrPainting r q.+1 (Hpq := ↓ Hrq) (Hq := Hq) (ε := ε) E d c =
  match (rew [id] mkPaintingType_step_computes in c) with
  | (l; c) => rew <- [id] C.(eqPaintingSp) in
      (mkRestrLayer r q l; mkRestrPainting r.+1 q.+1 E (d; l) c)
  end.
Proof.
  unfold mkRestrPainting; now rewrite le_induction'_step_computes.
Qed.

(** Now, for the last part of the proof: proving coherence conditions
    on [cohPainting] *)

(** The base case is easily discharged *)
Definition mkCohPainting_base {n} {C: νType n} {r q}
  {Hrq: r.+2 <= q.+2} {Hq: q.+2 <= n.+1} {ε ω}
  {D} {E: (mkFrame n.+1).(frame n.+1) D -> HSet}
  (d: (mkFrame r).(frame r) D) (c: mkPaintingType n r E d):
  rew [mkPaintingPrev.(painting'')] (mkFrame r).(cohFrame) r q d in
    mkPaintingPrev.(restrPainting') r q ε
      (mkRestrPainting r r (ε := ω) E d c) =
  mkPaintingPrev.(restrPainting') r r ω
    (mkRestrPainting r q.+1 (ε := ε) E d c).
Proof.
  rewrite mkRestrPainting_base_computes, mkRestrPainting_step_computes.
  destruct (rew [id] mkPaintingType_step_computes in c) as (l, c'); clear c.
  now exact (C.(eqRestrPainting0) (mkRestrPainting r.+1 q.+1 E (_; _) c')).
Qed.

(** A small abbreviation *)
Definition mkCohPaintingHyp {n} {C: νType n}
  p r q {Hpr: p.+2 <= r.+3} {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1}
  ε ω {D} {E: (mkFrame n.+1).(frame n.+1) D -> HSet}
  {d: (mkFrame p).(frame p) D}
  (c: mkPaintingType n p E d) :=
  rew [mkPaintingPrev.(painting'')] (mkFrame p).(cohFrame) r.+1 q.+1 d in
  C.(Painting).(restrPainting) p q.+1 (ε := ε)
    (mkRestrPainting p r.+1 E d c) =
  C.(Painting).(restrPainting) p r.+1 (ε := ω)
    (mkRestrPainting p q.+2 (ε := ε) E d c).

(** The step case is discharged as (mkCohLayer; IHP) *)
Definition mkCohPainting_step {n} {C: νType n} {p r q} {Hpr: p.+3 <= r.+3}
  {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1} {ε ω}
  {D} {E: (mkFrame n.+1).(frame n.+1) D -> HSet}
  {d: (mkFrame p).(frame p) D} {c: mkPaintingType n p E d}
  {IHP: forall (d: (mkFrame p.+1).(frame p.+1) D)
        (c: mkPaintingType n p.+1 E d), mkCohPaintingHyp p.+1 r q ε ω c}:
        mkCohPaintingHyp p r q ε ω c.
Proof.
  unfold mkCohPaintingHyp in *.
  do 2 rewrite mkRestrPainting_step_computes.
  destruct (rew [id] mkPaintingType_step_computes in c) as (l, c'); clear c.
  rewrite (C.(eqRestrPaintingSp) p q), (C.(eqRestrPaintingSp) p r).
  rewrite <- rew_permute_rl with (H := C.(@eqPaintingSp' _) _ _ _).
  f_equal.
  unshelve eapply (rew_existT_curried
    (Q := fun x =>
      C.(PaintingPrev).(painting') (rew <- [id] C.(eqFrameSp') in x))).
  - now exact (mkCohLayer l).
  - rewrite <- IHP with (d := (d; l)) (c := c').
    simpl (mkFrame p.+1). unfold mkPaintingPrev, painting''.
    unfold mkFrameSp, cohFrame.
    rewrite rew_map with (P := fun x => C.(PaintingPrev).(painting') x)
                       (f := fun x => rew <- [id] C.(eqFrameSp') in x).
    repeat rewrite rew_compose.
    repeat rewrite <- eq_trans_assoc.
    now rewrite eq_trans_sym_inv_l, eq_trans_refl_r.
Qed.

(** Build a [PaintingBlock n.+1] using what we just defined *)
#[local]
Instance mkPainting {n} {C: νType n}:
  PaintingBlock n.+1 mkPrefix mkPaintingPrev mkFrame.
  unshelve esplit; intros p.
  * intros *; now apply mkPaintingType.
  * intros q Hpq Hq ε d; now exact (mkRestrPainting p q).
  * intros *. revert d c. pattern p, Hpr. apply le_induction''.
    + now exact mkCohPainting_base.
    + clear p Hpr; unfold mkPaintingPrev, restrPainting'; cbv beta iota;
      intros p Hpr IHP d c; invert_le Hpr; invert_le Hrq.
      now exact (mkCohPainting_step (IHP := IHP)).
Defined.

(** The base case of a ν-parametric set (truncated at dimension 0) *)

#[local]
Instance mkνType0: νType 0.
  unshelve esplit.
  - now exact hunit.
  - unshelve esplit.
    * intros; now le_contra Hp.
    * intros; now le_contra Hp.
    * intros;now le_contra Hq.
  - unshelve esplit.
    * intros Hp _; now exact hunit.
    * intros; now le_contra Hq.
    * intros; now le_contra Hq.
  - unshelve esplit; intros.
    * now le_contra Hp.
    * now le_contra Hp.
    * now le_contra Hq.
  - unshelve esplit.
    * intros p Hp D E d. now exact (E d).
    * intros; now le_contra Hq.
    * intros; now le_contra Hq.
  - now intros.
  - intros; now le_contra len1.
  - intros; now le_contra Hp.
  - intros; now le_contra Hp.
  - intros; now le_contra Hq.
  - intros; now le_contra Hp.
  - intros; now le_contra Hp.
  - intros; now le_contra Hq.
  - intros; now le_contra Hp.
  - intros; now le_contra Hq.
Defined.

(** We are now ready to build an [νType n.+1] from an [νType n] *)
#[local]
Instance mkνTypeSn {n} (C: νType n): νType n.+1 :=
{|
    prefix := mkPrefix;
    FramePrev := mkFramePrev;
    Frame := mkFrame;
    PaintingPrev := mkPaintingPrev;
    Painting := mkPainting;
    eqFrame0 := ltac:(now intros *);
    eqFrame0' := ltac:(intros *; now apply C.(eqFrame0));
    eqFrameSp := ltac:(now intros *);
    eqFrameSp' := ltac:(intros *; now apply C.(eqFrameSp));
    eqRestrFrame0 := ltac:(now intros *);
    eqRestrFrameSp := ltac:(now intros *);
    eqPaintingSp := ltac:(intros *; now apply mkPaintingType_step_computes);
    eqPaintingSp' := ltac:(intros *; now apply C.(eqPaintingSp));
    eqRestrPainting0 := ltac:(intros *; simpl;
      now rewrite mkRestrPainting_base_computes, rew_rew');
    eqRestrPaintingSp := ltac:(intros *; simpl;
      now rewrite mkRestrPainting_step_computes, rew_rew');
|}.

(** An [νType] truncated up to dimension [n] *)
Fixpoint νTypeAt n: νType n :=
  match n with
  | O => mkνType0
  | n.+1 => mkνTypeSn (νTypeAt n)
  end.

(** The coinductive suffix of an [νType] beyond level [n] *)
CoInductive νTypeFrom n (X: (νTypeAt n).(prefix)): Type@{m'} := cons {
  this: (νTypeAt n).(Frame).(frame n) X -> HSet;
  next: νTypeFrom n.+1 (X; this);
}.

Arguments this {n X} _ d.
Arguments next {n X} _.

(** The final construction *)
Definition νTypes := νTypeFrom 0 tt.

(** Degeneracies *)

Class mkRefl T := intro_mkrefl : T -> Type@{m'}.
Class mk {T} (f: T -> Type@{m'}) (t: T) := intro_mk : f t.

Class DgnFrameBlockPrev {n'} (C: νType n'.+1)
  {reflPrefix: mkRefl C.(prefix)} := {
  reflFrame' p {Hp: p.+2 <= n'.+1} {D} {R: mk reflPrefix D}:
    C.(FramePrev).(frame'') p D -> C.(FramePrev).(Frames) p D;
}.

Arguments reflFrame' {n' C reflPrefix} _ p {Hp D R} d.

Class DgnFrameBlock {n'} (C: νType n'.+1) {reflPrefix: mkRefl C.(prefix)}
  p (Prev: DgnFrameBlockPrev C) := {
  reflFrame {Hp: p.+1 <= n'.+1} {D} {R: mk reflPrefix D}:
    C.(FramePrev).(Frames) p D -> C.(Frame).(frame p) D;
  idReflRestrFrame {ε} {Hp: p.+1 <= n'.+1} {D} {R: mk reflPrefix D}
    {d: C.(FramePrev).(Frames) p D}:
    C.(Frame).(restrFrame) n' ε (reflFrame d) = d;
  cohReflRestrFrame q {ε} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n'.+1} {D}
    {R: mk reflPrefix D} {d: C.(FramePrev).(Frames) p D}:
    Prev.(reflFrame') p (C.(FramePrev).(restrFrame') p q ε d) =
      C.(Frame).(restrFrame) q ε (reflFrame d);
}.

Arguments reflFrame {n' C reflPrefix p Prev} _ {Hp D R} d.
Arguments idReflRestrFrame {n' C reflPrefix p Prev} _ {ε Hp D R d}.
Arguments cohReflRestrFrame {n' C reflPrefix p Prev} _ q {ε Hpq Hq D R d}.

Class DgnPaintingBlockPrev {n'} (C: νType n'.+1) {reflPrefix: mkRefl C.(prefix)}
  (Prev: DgnFrameBlockPrev C) := {
  reflPainting' p {Hp: p.+2 <= n'.+1} {D} {R: mk reflPrefix D}
    {d: C.(FramePrev).(frame'') p D}:
    C.(PaintingPrev).(painting'') d ->
    C.(PaintingPrev).(painting') (Prev.(reflFrame') p d);
}.

Arguments reflPainting' {n' C reflPrefix Prev} _ p {Hp D R d} c.

Class HasRefl {n'} {C: νType n'.+1} {reflPrefix: mkRefl C.(prefix)}
  {DgnFramePrev: DgnFrameBlockPrev C}
  {DgnFrame: forall {p}, DgnFrameBlock C p DgnFramePrev} {D}
  {R: mk reflPrefix D} (E: _ -> HSet) :=
  hasRefl: forall (d: C.(FramePrev).(Frames) n' D)
    (c: C.(PaintingPrev).(painting') d),
    let l ε :=
      rew <- [C.(PaintingPrev).(painting')] DgnFrame.(idReflRestrFrame) in c in
     E (rew <- [id] C.(eqFrameSp) in (DgnFrame.(reflFrame) d; l)).

Class DgnPaintingBlock {n'} (C: νType n'.+1) {reflPrefix: mkRefl C.(prefix)}
  {Q: DgnFrameBlockPrev C}
  (Prev: DgnPaintingBlockPrev C Q)
  (FrameBlock: forall {p}, DgnFrameBlock C p Q) := {
  reflPainting p {Hp: p.+1 <= n'.+1} {D} {R: mk reflPrefix D} {E}
    {L: HasRefl E} {d: C.(FramePrev).(Frames) p D}:
    C.(PaintingPrev).(painting') d ->
    C.(Painting).(painting) E (FrameBlock.(reflFrame) d);
  idReflRestrPainting {p ε} {Hp: p.+1 <= n'.+1} {D} {R: mk reflPrefix D}
    {E} {L: HasRefl E}
    {d: C.(FramePrev).(Frames) p D} {c: C.(PaintingPrev).(painting') d}:
    rew [C.(PaintingPrev).(painting')] FrameBlock.(idReflRestrFrame) in
    C.(Painting).(restrPainting) p n' (ε := ε) (E := E) (reflPainting p c) = c;
  cohReflRestrPainting {p} q {ε} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n'.+1} {D}
    {R: mk reflPrefix D} {E} {L: HasRefl E} {d: C.(FramePrev).(Frames) p D}
    {c: C.(PaintingPrev).(painting') d}:
    rew <- [C.(PaintingPrev).(painting')] FrameBlock.(cohReflRestrFrame) q in
    C.(Painting).(restrPainting) p q (ε := ε) (E := E) (reflPainting p c) =
    Prev.(reflPainting') p (C.(PaintingPrev).(restrPainting') _ q ε c);
}.

Arguments reflPainting {n' C reflPrefix Q Prev FrameBlock} _ p {Hp D R E L d} c.
Arguments idReflRestrPainting {n' C reflPrefix Q Prev FrameBlock} _ {p ε Hp D R
  E L d c}.
Arguments cohReflRestrPainting {n' C reflPrefix Q Prev FrameBlock} _ {p} q
  {ε Hpq Hq D R E L d c}.

(** Dgn is the extra structure to support degeneracies, which we call Refl *)

Class Dgn {n'} (C: νType n'.+1) := {
  ReflPrefix: mkRefl C.(prefix);
  DgnFramePrev: DgnFrameBlockPrev C;
  DgnFrame {p}: DgnFrameBlock C p DgnFramePrev;
  DgnPaintingPrev: DgnPaintingBlockPrev C DgnFramePrev;
  DgnPainting: DgnPaintingBlock C DgnPaintingPrev (@DgnFrame);
  ReflLayer {p} {Hp: p.+2 <= n'.+1} {D} {R: mk ReflPrefix D}
    {d: C.(FramePrev).(Frames) p D}
    (l: C.(layer') d): C.(Layer) (DgnFrame.(reflFrame) d) :=
    fun ε => rew [C.(PaintingPrev).(painting')]
    DgnFrame.(cohReflRestrFrame) p in DgnPaintingPrev.(reflPainting') p (l ε);
  eqReflFrameSp {p q} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n'.+1} {D}
    {R: mk ReflPrefix D} {d: C.(FramePrev).(Frames) p D} (l: C.(layer') d):
    DgnFrame.(reflFrame) (rew <- [id] C.(eqFrameSp') in (d; l)) =
    rew <- [id] C.(eqFrameSp) in (DgnFrame.(reflFrame) d; ReflLayer l);
  eqReflPaintingSp p q {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n'.+1} {D}
    {R: mk ReflPrefix D} {E} {L: HasRefl E} {d} {l: C.(layer') d}
    {c: C.(PaintingPrev).(painting') (D := D)
      (rew <- [id] C.(eqFrameSp') in (d; l))}:
    DgnPainting.(reflPainting) p (rew <- [id] C.(eqPaintingSp') in (l; c)) =
    rew <- [id] C.(eqPaintingSp) in
      (ReflLayer l; rew [C.(Painting).(painting) E] eqReflFrameSp l in
        DgnPainting.(reflPainting) p.+1 c);
}.

Arguments ReflPrefix {n' C} _.
Arguments DgnFramePrev {n' C} _.
Arguments DgnFrame {n' C} _ {p}.
Arguments DgnPaintingPrev {n' C} _.
Arguments DgnPainting {n' C} _.
Arguments ReflLayer {n' C} _ {p Hp D R d} l.
Arguments eqReflFrameSp {n' C} _ {p q Hpq Hq D R d} l.
Arguments eqReflPaintingSp {n' C} _ p q {Hpq Hq D R E L d l c}.

#[local]
Instance mkReflPrefix {n'} {C: νType n'.+1} {G: Dgn C}: mkRefl
  (mkνTypeSn C).(prefix) :=
  fun D => { R : mk G.(ReflPrefix) D.1 &_T
  HasRefl (DgnFrame := fun p => G.(DgnFrame)) D.2 }.

#[local]
Instance mkDgnFramePrev {n'} {C: νType n'.+1} {G: Dgn C}:
  DgnFrameBlockPrev (mkνTypeSn C) := {|
  reflFrame' p Hp (D: (mkνTypeSn C).(prefix)) R :=
    G.(DgnFrame).(reflFrame) (R := R.1);
|}.

Definition mkReflLayer {n' p} {C: νType n'.+1} {G: Dgn C}
  {Hp: p.+2 <= n'.+2} {Frame: DgnFrameBlock (mkνTypeSn C) p mkDgnFramePrev}
  {D} {R: mk mkReflPrefix D} {d: mkFramePrev.(Frames) p D} (l: mklayer' d):
  mkLayer (Frame.(reflFrame) d) :=
  fun ω => rew [C.(Painting).(painting) D.2]
    Frame.(cohReflRestrFrame) p in G.(DgnPainting).(reflPainting) (L := R.2) p
    (l ω).

Definition mkIdReflRestrLayer {n' p ε} {C: νType n'.+1} {G: Dgn C}
  {Hp: p.+2 <= n'.+2}
  {FrameBlock: DgnFrameBlock (mkνTypeSn C) p mkDgnFramePrev} {D}
  {R: mk mkReflPrefix D} {d: mkFramePrev.(Frames) p D} {l: mklayer' d}:
  rew [mklayer'] FrameBlock.(idReflRestrFrame) (ε := ε) in
    mkRestrLayer p n' (mkReflLayer l) = l.
Proof.
  apply functional_extensionality_dep; intros 𝛉.
  unfold mkRestrLayer, mkReflLayer.
  rewrite <-
    (G.(DgnPainting).(idReflRestrPainting) (L := R.2)
      (ε := ε) (E := D.2) (c := l 𝛉)).
  rewrite <- map_subst_app, <- map_subst.
  rewrite rew_map with
    (P := fun x => C.(PaintingPrev).(painting') x),
  rew_map with
    (P := fun x => C.(PaintingPrev).(painting') x)
    (f := fun d => C.(Frame).(restrFrame) n' ε d).
  repeat rewrite rew_compose.
  apply rew_swap with
    (P := fun x => C.(PaintingPrev).(painting') x).
  rewrite rew_app_rl. now trivial.
  now apply (C.(FramePrev).(Frames) p D.1).(UIP).
Defined.

Definition mkCohReflRestrLayer {n' p} q {ε} {C: νType n'.+1} {G: Dgn C}
  {Hp: p.+3 <= q.+3} {Hq: q.+3 <= n'.+2}
  {FrameBlock: DgnFrameBlock (mkνTypeSn C) p mkDgnFramePrev} {D}
  {R: mk mkReflPrefix D} {d: mkFramePrev.(Frames) p D} {l: mklayer' (C := C) d}:
    rew [mklayer'] FrameBlock.(cohReflRestrFrame) q.+1 in
     G.(ReflLayer) (C.(RestrLayer) p q ε l) = mkRestrLayer p q (mkReflLayer l).
Proof.
  apply functional_extensionality_dep; intros 𝛉.
  unfold RestrLayer, mkRestrLayer, ReflLayer, mkReflLayer.
  rewrite <- map_subst_app, <- !map_subst.
  rewrite rew_map with
    (P := fun x => C.(PaintingPrev).(painting') x),
  rew_map with
    (P := fun x => C.(PaintingPrev).(painting') x)
    (f := fun d => C.(Frame).(restrFrame) q ε d),
  rew_map with
    (P := fun x => C.(PaintingPrev).(painting') x)
    (f := fun x => G.(DgnFramePrev).(reflFrame') p x).
  rewrite <- (G.(DgnPainting).(cohReflRestrPainting) q (L := R.2)
    (E := D.2)).
  repeat rewrite rew_compose.
  apply rew_swap with
    (P := fun x => C.(PaintingPrev).(painting') x).
  rewrite rew_app_rl. now trivial.
  now apply (C.(FramePrev).(Frames) p D.1).(UIP).
Defined.

#[local]
Instance mkDgnFrame0 {n'} {C: νType n'.+1} {G: Dgn C}:
  DgnFrameBlock (mkνTypeSn C) O mkDgnFramePrev.
  unshelve esplit.
  * intros; now exact tt.
  * intros; apply rew_swap with (P := id); now destruct (rew <- _ in _).
  * intros; apply rew_swap with (P := id); now destruct (rew _ in _).
Defined.

#[local]
Instance mkDgnFrameSp {n' p} {C: νType n'.+1} {G: Dgn C}
  {Frame: DgnFrameBlock (mkνTypeSn C) p mkDgnFramePrev}:
  DgnFrameBlock (mkνTypeSn C) p.+1 mkDgnFramePrev.
  unshelve esplit.
  * (* reflFrame *)
    intros Hp D R d'.
    destruct (rew [id] (mkνTypeSn C).(eqFrameSp') in d') as (d, l); clear d'.
    now exact (Frame.(reflFrame) d; mkReflLayer l).
  * (* idReflRestrFrame *)
    simpl; intros ε Hp D R d'.
    rewrite <- rew_opp_l with (P := id) (H := C.(eqFrameSp)).
    destruct (rew [id] _ in d') as (d, l); clear d'.
    f_equal.
    now exact (= Frame.(idReflRestrFrame); mkIdReflRestrLayer).
  * (* cohReflRestrFrame *)
    intros q ε Hpq Hq D R d'; simpl. invert_le Hpq. invert_le Hq.
    rewrite <- rew_opp_l with (P := id) (H := C.(eqFrameSp)) (a := d'),
            rew_opp_r.
    destruct (rew [id] _ in d') as (d, l); clear d'.
    rewrite C.(eqRestrFrameSp), G.(eqReflFrameSp).
    f_equal.
    now exact (= Frame.(cohReflRestrFrame) q.+1; mkCohReflRestrLayer q).
Defined.

#[local]
Instance mkDgnFrame {n' p} {C: νType n'.+1} {G: Dgn C}:
  DgnFrameBlock (mkνTypeSn C) p mkDgnFramePrev.
  induction p.
  * now exact mkDgnFrame0.
  * now exact mkDgnFrameSp.
Defined.

#[local]
Instance mkDgnPaintingPrev {n'} {C: νType n'.+1} {G: Dgn C}:
  DgnPaintingBlockPrev (mkνTypeSn C) mkDgnFramePrev := {|
  reflPainting' p Hp (D: (mkνTypeSn C).(prefix)) (R: mk mkReflPrefix D) d c :=
    G.(DgnPainting).(reflPainting) p c (L := R.2);
|}.

Definition mkReflPainting {n'} p {C: νType n'.+1} {G: Dgn C}
  {Hp: p.+1 <= n'.+2} {D} {R: mk mkReflPrefix D} {E} {L: HasRefl E}
  {d: mkFramePrev.(Frames) p D} (c: mkPaintingPrev.(painting') d):
  mkPaintingType n'.+1 p E (mkDgnFrame.(reflFrame) d).
Proof.
  revert d c; apply le_induction' with (Hp := Hp); clear p Hp.
  * intros d c. rewrite mkPaintingType_step_computes. unshelve esplit.
    - now exact (fun ε : arity => rew <- [mkPaintingPrev.(painting')]
        (mkDgnFrame).(idReflRestrFrame) (ε := ε) in c).
    - rewrite mkPaintingType_base_computes.
      now exact (L d c).
  * intros p Hp IHP d c.
    destruct (rew [id] C.(eqPaintingSp) in c) as (l, c').
    simpl in IHP; specialize (IHP (rew <- [id] C.(eqFrameSp) in (d; l)) c').
    rewrite rew_rew' in IHP.
    rewrite mkPaintingType_step_computes.
    unshelve esplit.
    - now exact (mkReflLayer l).
    - now apply IHP.
Defined.

Lemma mkReflPainting_base_computes {n'} {C: νType n'.+1} {G: Dgn C} {D}
  {R: mk mkReflPrefix D} {E} {L: HasRefl E} {d: mkFramePrev.(Frames) n'.+1 D}
  {c: mkPaintingPrev.(painting') d}:
  mkReflPainting n'.+1 (E := E) c =
  rew <- [id] mkPaintingType_step_computes in
    ((fun ε : arity => rew <- [mkPaintingPrev.(painting')]
      (mkDgnFrame).(idReflRestrFrame) (ε := ε) in c);
    rew <- mkPaintingType_base_computes in L d c).
Proof.
  unfold mkReflPainting; now rewrite le_induction'_base_computes.
Qed.

Lemma mkReflPainting_step_computes {n' p} {C: νType n'.+1} {G: Dgn C}
  {Hp: p.+2 <= n'.+2} {D} {R: mk mkReflPrefix D}
  {E} {L: HasRefl E} {d: mkFramePrev.(Frames) p D}
  {c: mkPaintingPrev.(painting') d}:
  mkReflPainting p (E := E) c = match (rew [id] C.(eqPaintingSp) in c) with
  | (l; c') => rew <- [id] mkPaintingType_step_computes in
    (mkReflLayer l;
    rew [fun d => mkPaintingType n'.+1 p.+1 E match d with
          (d'; l) => (mkDgnFrame.(reflFrame) d'; mkReflLayer l)
        end] rew_rew' C.(eqFrameSp) id in mkReflPainting p.+1 (E := E) c')
  end.
Proof.
  unfold mkReflPainting; now rewrite le_induction'_step_computes.
Qed.

#[local]
Instance mkDgnPainting {n'} {C: νType n'.+1} {G: Dgn C}:
  DgnPaintingBlock (mkνTypeSn C) mkDgnPaintingPrev (fun p => mkDgnFrame).
  unshelve esplit.
  - (* reflPainting *)
    intros. apply mkReflPainting.
    * now exact L.
    * now exact X.
  - (* idReflRestrPainting *)
    intros. revert d c. pattern p, Hp; apply le_induction'; clear p Hp.
    * intros d c; simpl (mkνTypeSn C).(Painting).(restrPainting); cbv beta.
      rewrite mkRestrPainting_base_computes, mkReflPainting_base_computes.
      now repeat rewrite rew_rew'.
    * intros p Hp IHP d c. simpl.
      rewrite mkRestrPainting_step_computes, mkReflPainting_step_computes.
      (* Coq bug? Why doesn't a direct destruct work? *)
      transitivity (rew <- [id] C.(eqPaintingSp) in rew [id] C.(eqPaintingSp) in c).
      2: now rewrite rew_rew.
      set (c' := rew [id] C.(eqPaintingSp) in c).
      change (rew [id] C.(eqPaintingSp) in c) with c'.
      destruct c' as (l, c''). clear c; rename c'' into c.
      rewrite rew_rew'.
      rewrite <- rew_permute_rl with (H := C.(@eqPaintingSp _) _ _ _ _).
      f_equal.
      unshelve eapply (rew_existT_curried
        (Q := fun x =>
          C.(Painting).(painting) _ (rew <- [id] C.(eqFrameSp) in x))).
      + now exact mkIdReflRestrLayer.
      + rewrite <- IHP,
                rew_map with
                  (P := fun x => C.(Painting).(painting) D.2 x)
                  (f := fun x => rew <- [id] C.(eqFrameSp) in x).
        apply rew_swap_rl with (P := C.(Painting).(painting) D.2).
        rewrite rew_compose.
        simpl (mkνTypeSn C).(Painting).(restrPainting). cbv beta.
        set (h := fun d => match d with (d'; l') =>
            (mkDgnFrame.(reflFrame) d' as a in (mkFrame p).(frame _) D;
             mkReflLayer l' in mkLayer a)
            end).
        set (e' := rew_rew' _ _);
        rewrite <- (map_subst (P := fun d => mkPaintingType n'.+1 p.+1 E (h d))
            (fun d c => mkRestrPainting p.+1 n'.+1 E _ c) e' _); subst e'.
        rewrite rew_map with
            (P := fun x => (mkPaintingPrev.(painting') x).(Dom))
            (f := fun x => (mkFrame p.+1).(restrFrame) n'.+1 _ (h x)).
        apply rew_swap_rl with (P := C.(Painting).(painting) D.2),
              rew_app_rl_opp with (P := fun x => C.(Painting).(painting) D.2 x).
        now apply (C.(Frame).(frame p.+1) D.1).(UIP).
  - (* cohReflRestrPainting *)
    intros; simpl.
    revert d c. pattern p, Hpq; apply le_induction''; clear p Hpq.
    * intros d c; simpl.
      rewrite mkRestrPainting_base_computes, mkReflPainting_step_computes.
      set (c' := rew [id] C.(eqPaintingSp) in c).
      change (rew [id] C.(eqPaintingSp) in c) with c'.
      replace c with (rew <- [id] C.(eqPaintingSp) in c') by apply rew_rew.
      destruct c' as (l, c''); clear c; rename c'' into c.
      rewrite rew_rew', rew_rew.
      now rewrite (C.(eqRestrPainting0) c).
    * intros p Hp IHP d c; simpl. invert_le Hp.
      rewrite mkRestrPainting_step_computes, mkReflPainting_step_computes.
      set (c' := rew [id] C.(eqPaintingSp) in c).
      change (rew [id] C.(eqPaintingSp) in c) with c'.
      replace c with (rew <- [id] C.(eqPaintingSp) in c') by apply rew_rew.
      destruct c' as (l, c''); clear c; rename c'' into c.
      rewrite rew_rew',
              (C.(eqRestrPaintingSp) p q),
              (G.(eqReflPaintingSp) p q),
              <- rew_permute_rr with (H := C.(@eqPaintingSp _) _ _ _ _).
      f_equal.
      unshelve eapply (rew_existT_curried
        (Q := fun x =>
          C.(Painting).(painting) _ (rew <- [id] C.(eqFrameSp) in x))).
      + now rewrite <- mkCohReflRestrLayer with (d := d), rew_compose,
                       eq_trans_sym_inv_r.
      + rewrite <- map_subst, <- IHP.
        apply rew_swap_rl with
            (P := fun x => C.(Painting).(painting) D.2
            (rew <- [id] C.(eqFrameSp) in x)).
        set (h := fun d => match d with (d'; l') =>
            (mkDgnFrame.(reflFrame) d' as a in (mkFrame p).(frame _) D;
             mkReflLayer l' in mkLayer a)
            end).
        set (e' := rew_rew' _ _);
        rewrite <- (map_subst (P := fun d => mkPaintingType n'.+1 p.+1 E (h d))
            (fun d c => mkRestrPainting p.+1 q.+1 E _ c) e' _); subst e'.
        set (P := fun x => (C.(Painting).(painting) D.2 x).(Dom)).
        rewrite rew_map with (P := P) (f := G.(DgnFrame).(reflFrame)),
                rew_map' with (P := P)
                  (f := fun x => rew <- [id] C.(eqFrameSp) in x),
                rew_map with (P := P)
                  (f := fun d => ((mkFrame p.+1).(restrFrame) q.+1 ε (h d))).
        apply rew_swap_rl with (P := P).
        rewrite rew_compose_rl,
                rew_compose_lr with (P := P).
        set (t0 := eq_trans _ _); set (t1 := eq_trans _ _);
        clearbody t0; clearbody t1.
        repeat rewrite rew_compose.
        now rewrite ((C.(Frame).(frame p.+1) D.1).(UIP)
            (h := eq_trans _ _) (g := eq_refl)).
Defined.

#[local]
Instance mkDgn0: Dgn (νTypeAt 1).
Proof.
  unshelve esplit.
  - intro. now exact hunit.
  - split; intros; now le_contra Hp.
  - intros; unshelve esplit.
    * simpl; intros; invert_le Hp. now exact tt.
    * simpl; intros; invert_le Hp; destruct d. now exact eq_refl.
    * simpl; intros; now le_contra Hq.
  - split; intros; now le_contra Hp.
  - intros; unshelve esplit.
    * simpl; intros * L * c; invert_le Hp; destruct d.
      rewrite mkPaintingType_step_computes. unshelve esplit. now trivial.
      rewrite mkPaintingType_base_computes. now exact (L tt c).
    * simpl; intros; invert_le Hp; destruct d. simpl.
      now rewrite mkRestrPainting_base_computes, rew_rew'.
    * simpl; intros; now le_contra Hq.
  - intros; now le_contra Hq.
  - intros; now le_contra Hq.
Defined.

#[local]
Instance mkDgnSn {n'} {C: νType n'.+1}:
  Dgn C -> Dgn (mkνTypeSn C).
Proof.
  unshelve esplit.
  - intros; simpl; now rewrite rew_rew'.
  - intros; simpl. rewrite mkReflPainting_step_computes, rew_rew'.
    change (eq_ind_r (x := ?x) ?P) with (eq_rect_r (x := x) P).
    now rewrite rew_map with (P := mkPaintingType n'.+1 p.+1 E), rew_eq_refl.
Defined.

Fixpoint νDgnTypeAt n': Dgn (νTypeAt n'.+1) :=
  match n' with
  | O => mkDgn0
  | n'.+1 => mkDgnSn (νDgnTypeAt n')
  end.

CoInductive νDgnTypeFrom n' (X: (νTypeAt n'.+1).(prefix)) (M: νTypeFrom n'.+1 X)
  (L: (νDgnTypeAt n').(ReflPrefix) X): Type@{m'} := cons' {
  dgn: HasRefl M.(this);
  dgnNext: νDgnTypeFrom n'.+1 (X; M.(this)) M.(next) (L; dgn);
}.

Definition νDgnTypes (X: νTypes) := νDgnTypeFrom 0 (tt; X.(this)) X.(next) tt.
End νType.

Definition AugmentedSemiSimplicial := νTypes hunit.
Definition SemiSimplicial := νTypeFrom hunit 1 (tt; fun _ => hunit).
Definition SemiCubical := νTypes hbool.
Definition AugmentedSimplicial := { X &_T νDgnTypes hunit X }.
Definition Cubical := { X &_T νDgnTypes hbool X }.

(** Some examples *)

Notation "{ x : A && P }" := (sigT (A := A) (fun x => P)): type_scope.

Example SemiSimplicial2 := Eval lazy -[projT2] in
 (νTypeAt hunit 2).(prefix _).
Print SemiSimplicial2.

Example SemiCubical2 := Eval lazy -[projT2] in
 (νTypeAt hbool 2).(prefix _).
Print SemiCubical2.

Example Simplicial1 := Eval lazy -[projT1 projT2] in
 (νDgnTypeAt hunit 1).(ReflPrefix _).
Print Simplicial1.

Example Cubical1 := Eval lazy -[projT1 projT2] in
 (νDgnTypeAt hbool 1).(ReflPrefix _).
Print Cubical1.
