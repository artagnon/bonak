(** An "indexed" construction of N-parametric sets
    For N=1, this builds augmented semi-simplicial sets
    For N=2, this builds semi-cubical sets *)

Import Logic.EqNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Aux.
Require Import RewLemmas.

(* Note: this import overrides { & } notation and introduces hforall *)
Set Warnings "-notation-overridden".
Require Import HSet.

Require Import Yoneda.

Set Printing Projections.
Set Keyed Unification.
Remove Printing Let sigT.
Remove Printing Let prod.

(** The universe where the N-parametric sets live *)
Universe m.

(** The universe where the type of N-parametric sets live *)
Universe m'.

Section NType.
(** The arity [N] of parametric sets *)
Variable side: HSet.

(*********************************************)
(** A N-parametric set is a family of sets obtained by iterating
    Reynolds' parametricity translation.

    For N=1: this is a collection of colors, of points depending on a
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

    For N=2: this is a collection of points, of lines connecting two
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

(***********)
(** Frames *)

(** The construction maintains at each step of the induction the three
    last levels of frames (called [frame''], [frame'], [frame]), the
    two restrictions between them (called [restrFrame'] and
    [restrFrame]) and the coherence between these two restrictions
    (called [cohFrame]). *)

(** [PartialFramePrev] consists of the levels we remember before the
    current one and for each such previous data, [PartialFrame]
    consists of the data to maintain at the current level. *)
Class PartialFramePrev (n: nat) (prefix: Type@{m'}) := {
  frame' {p} (Hp: p.+1 <= n): prefix -> HSet@{m};
  frame'' {p} (Hp: p.+2 <= n): prefix -> HSet@{m};
  restrFrame' {p q} {Hpq: p.+2 <= q.+2} (Hq: q.+2 <= n) (ε: side) {D: prefix}:
    frame' (↓ (Hpq ↕ Hq)) D -> frame'' (Hpq ↕ Hq) D;
}.

Arguments frame' {n prefix} _ {p} Hp D.
Arguments frame'' {n prefix} _ {p} Hp D.
Arguments restrFrame' {n prefix} _ {p q Hpq} Hq ε {D} d.

Class PartialFrame (n p: nat) (prefix: Type@{m'})
  (FramePrev: PartialFramePrev n prefix) := {
  frame (Hp: p <= n): prefix -> HSet@{m};
  restrFrame {q} {Hpq: p.+1 <= q.+1} (Hq: q.+1 <= n) (ε: side) {D: prefix}:
    frame (↓ (Hpq ↕ Hq)) D -> FramePrev.(frame') (Hpq ↕ Hq) D;
  cohFrame {q r} {Hpr: p.+2 <= r.+2} {Hrq: r.+2 <= q.+2} {Hq: q.+2 <= n}
    {ε: side} {ω: side} {D: prefix} (d: frame (↓ (⇓ Hpr ↕ (↓ (Hrq ↕ Hq)))) D):
    FramePrev.(restrFrame') (Hpq := Hpr ↕ Hrq) Hq ε
      (restrFrame (Hpq := ⇓ Hpr) (↓ (Hrq ↕ Hq)) ω d) =
    (FramePrev.(restrFrame') (Hpq := Hpr) (Hrq ↕ Hq) ω
      (restrFrame (Hpq := ↓ (Hpr ↕ Hrq)) Hq ε d));
}.

Arguments frame {n p prefix FramePrev} _ Hp D.
Arguments restrFrame {n p prefix FramePrev} _ {q Hpq} Hq ε {D} d.
Arguments cohFrame {n p prefix FramePrev} _ {q r Hpr Hrq Hq ε ω D} d.
(* We want ε and ω to be printed, but have them inferred;
   Coq doesn't support this. *)

(************)
(** Fillers *)

(** We build fillers using an iterated construction: a filler at level n depends
    on fillers at level n-1 and n-2; just as we have frame' and frame'', we have
    filler' and filler''. *)
Class PartialFillerPrev (n: nat) (prefix: Type@{m'})
  (FramePrev : PartialFramePrev n prefix) := {
  filler' {p} {Hp: p.+1 <= n} {D: prefix}: FramePrev.(frame') Hp D -> HSet@{m};
  filler'' {p} {Hp: p.+2 <= n} {D: prefix}: FramePrev.(frame'') Hp D -> HSet@{m};
  restrFiller' {p q} {Hpq: p.+2 <= q.+2} (Hq: q.+2 <= n) (ε: side) {D: prefix}
    {d : FramePrev.(frame') (↓ (Hpq ↕ Hq)) D}:
    filler' d -> filler'' (FramePrev.(restrFrame') Hq ε d);
}.

Arguments filler' {n prefix FramePrev} _ {p Hp D} d.
Arguments filler'' {n prefix FramePrev} _ {p Hp D} d.
Arguments restrFiller' {n prefix FramePrev} _ {p q Hpq} Hq ε {D} [d] b.

(* Filler consists of filler, restrFiller, and coherence conditions between them *)
Class PartialFiller (n: nat) (prefix: Type@{m'})
  {FramePrev: PartialFramePrev n prefix}
  (FillerPrev: PartialFillerPrev n prefix FramePrev)
  (Frame: forall {p}, PartialFrame n p prefix FramePrev) := {
  filler {p} {Hp: p <= n} {D: prefix}:
    (Frame.(frame) (♢ _) D -> HSet@{m}) -> Frame.(frame) Hp D -> HSet@{m};
  restrFiller {p q} {Hpq: p.+1 <= q.+1}
    (Hq: q.+1 <= n) (ε: side) {D : prefix} {E: Frame.(frame) (♢ _) D -> HSet@{m}}
    {d: Frame.(frame) (↓ (Hpq ↕ Hq)) D} (c: filler E d):
    FillerPrev.(filler') (Frame.(restrFrame) Hq ε d);
  cohFiller {p q r} {Hpr: p.+2 <= r.+2}
    {Hrq: r.+2 <= q.+2} {Hq: q.+2 <= n}
    (ε: side) (ω : side) {D: prefix} (E: Frame.(frame) (♢ _) D -> HSet@{m})
    (d: Frame.(frame) (↓ (⇓ Hpr ↕ (↓ (Hrq ↕ Hq)))) D) (c: filler E d):
    rew [FillerPrev.(filler'')] (Frame.(cohFrame) d) in
    FillerPrev.(restrFiller') (Hpq := Hpr ↕ Hrq) Hq
    ε (restrFiller (Hpq := ⇓ Hpr) (↓ (Hrq ↕ Hq)) ω c) =
      (FillerPrev.(restrFiller') (Hpq := Hpr) (Hrq ↕ Hq)
      ω (restrFiller (Hpq := ↓ (Hpr ↕ Hrq)) Hq ε c));
}.

Arguments filler {n prefix FramePrev FillerPrev Frame} _ {p Hp D} E.
Arguments restrFiller {n prefix FramePrev FillerPrev Frame} _ {p q Hpq Hq ε D E} [d] c.
Arguments cohFiller {n prefix FramePrev FillerPrev Frame} _ {p q r Hpr Hrq Hq ε ω D E d} c.

(* An N-parametric type truncated at level [n] consists of:

  - a [prefix] of parametric types up to dimension [n],
  - a type of frames with their restrictions and coherence of
    restrictions [Frame] (depending on their values are dimension [n]-1
    and [n]-2) that are Σ-types of length [n] that is recursively built
    out by induction on some [p] ranging from 0 to [n]
  - a type of fillers (with their restrictions and coherence of
    restrictions) [Filler] (depending on their values [FillerPrev] at
    dimensions [n]-1 and [n]-2) that are also recursively built out from
    partial fillers
  - axioms characterizing the definition of [Frame] and [Filler] in
    the previous dimensions, so that the induction can be carried
*)

Class NType (n : nat) := {
  prefix: Type@{m'};
  FramePrev: PartialFramePrev n prefix;
  Frame {p}: PartialFrame n p prefix FramePrev;
  FillerPrev: PartialFillerPrev n prefix FramePrev;
  Filler: PartialFiller n prefix FillerPrev (@Frame);

  (** Abbreviations for [N]-family of previous fillers, one for
      each [ϵ]-restriction of the previous frame (ϵ∈N) *)
  Layer {p} {Hp: p.+1 <= n} {D: prefix} (d: Frame.(frame) (↓ Hp) D) :=
    hforall ε, FillerPrev.(filler') (Frame.(restrFrame) Hp ε d);
  Layer' {p} {Hp: p.+2 <= n} {D: prefix} (d: FramePrev.(frame') (↓ Hp) D) :=
    hforall ε, FillerPrev.(filler'') (FramePrev.(restrFrame') Hp ε d);
  RestrLayer {p q ε} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n} {D: prefix}
    (d: Frame.(frame) (↓ ↓ (Hpq ↕ Hq)) D) (l: Layer d):
      Layer' (Frame.(restrFrame) Hq ε d) :=
  fun ω => rew [FillerPrev.(filler'')] Frame.(cohFrame) (Hrq := Hpq) d in FillerPrev.(restrFiller') Hq ε (l ω);

  (* We can't create htt: hunit, so we have to resort to this *)
  eqFrame0 {len0: 0 <= n} {D: prefix}: (Frame.(frame) len0 D).(Dom) = unit;
  eqFrame0' {len1: 1 <= n} {D: prefix}: (FramePrev.(frame') len1 D).(Dom) = unit;
  eqFrameSp {p} {Hp: p.+1 <= n} {D: prefix}:
    Frame.(frame) Hp D = {d: Frame.(frame) (↓ Hp) D & Layer d} :> Type;
  eqFrameSp' {p} {Hp: p.+2 <= n} {D: prefix}:
    FramePrev.(frame') Hp D = {d : FramePrev.(frame') (↓ Hp) D & Layer' d}
      :> Type;
  eqRestrFrame0 {q} {Hpq: 1 <= q.+1} {Hq: q.+1 <= n} {ε: side} {D: prefix}:
    Frame.(restrFrame) (Hpq := Hpq) Hq ε (rew <- [id] eqFrame0 (D := D) in tt) =
      (rew <- [id] eqFrame0' in tt);
  eqRestrFrameSp {ε p q} {D: prefix} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n}
    {d: Frame.(frame) (↓ ↓ (Hpq ↕ Hq)) D}
    {l: Layer (Hp := ↓ (Hpq ↕ Hq)) d}:
    Frame.(restrFrame) Hq ε (rew <- [id] eqFrameSp in (d; l)) =
      rew <- [id] eqFrameSp' in (Frame.(restrFrame) Hq ε d; RestrLayer d l);
  eqFillerSp {p} {Hp: p.+1 <= n} {D: prefix} {E d}:
    Filler.(filler) (Hp := ↓ Hp) E d = {l: Layer d &
      Filler.(filler) (D := D) E (rew <- [id] eqFrameSp in (d; l))} :> Type;
  eqFillerSp' {p} {Hp: p.+2 <= n} {D: prefix} {d}:
    FillerPrev.(filler') (Hp := ↓ Hp) d = {b : Layer' d &
      FillerPrev.(filler') (rew <- [id] eqFrameSp' (D := D) in (d; b))} :> Type;
  eqRestrFiller0 {p} {Hp: p.+1 <= n} {D: prefix} {E} {d} {ε: side}
    {l: Layer d} {Q: Filler.(filler) (D := D) E (rew <- eqFrameSp in (d; l))}:
      l ε = Filler.(restrFiller) (Hq := Hp) (rew <- [id] eqFillerSp in (l; Q));
  eqRestrFillerSp {p q} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n} {D: prefix} {E} {d}
    {ε: side} {l: Layer (Hp := ↓ (Hpq ↕ Hq)) d}
    {Q: Filler.(filler) (D := D) E (rew <- eqFrameSp in (d; l))}:
    Filler.(restrFiller) (Hpq := ↓ Hpq) (ε := ε) (rew <- [id] eqFillerSp in (l; Q)) = rew <- [id] eqFillerSp' (Hp := Hpq ↕ Hq) in
      (RestrLayer d l; rew [FillerPrev.(filler')] eqRestrFrameSp in
        Filler.(restrFiller) Q);
}.

Arguments prefix {n} _.
Arguments FramePrev {n} _.
Arguments FillerPrev {n} _.
Arguments Frame {n} _ {p}.
Arguments Filler {n} _.
Arguments Layer {n} _ {p Hp D} d.
Arguments Layer' {n} _ {p Hp D} d.
Arguments RestrLayer {n} _ {p q} ε {Hpq Hq D d} l.
Arguments eqFrame0 {n} _ {len0 D}.
Arguments eqFrame0' {n} _ {len1 D}.
Arguments eqFrameSp {n} _ {p Hp D}.
Arguments eqFrameSp' {n} _ {p Hp D}.
Arguments eqRestrFrame0 {n} _ {q Hpq Hq ε D}.
Arguments eqRestrFrameSp {n} _ {ε p q D Hpq Hq d l}.
Arguments eqFillerSp {n} _ {p Hp D E d}.
Arguments eqFillerSp' {n} _ {p Hp D d}.
Arguments eqRestrFiller0 {n} _ {p Hp D E d ε l Q}.
Arguments eqRestrFillerSp {n} _ {p q Hpq Hq D E d ε l Q}.

(***************************************************)
(** The construction of [NType n+1] from [NType n] *)

(** Extending the initial prefix *)
Definition mkprefix {n} {C: NType n}: Type@{m'} :=
  sigT (fun D : C.(prefix) => C.(Frame).(frame) (♢ _) D -> HSet@{m}).

(** Memoizing the previous levels of [Frame] *)
Definition mkFramePrev {n} {C: NType n}: PartialFramePrev n.+1 mkprefix := {|
  frame' (p: nat) (Hp: p.+1 <= n.+1) (D: mkprefix) := C.(Frame).(frame) (⇓ Hp) D.1;
  frame'' (p: nat) (Hp: p.+2 <= n.+1) (D: mkprefix) :=
    C.(FramePrev).(frame') (⇓ Hp) D.1;
  restrFrame' (p q: nat) (Hpq: p.+2 <= q.+2) (Hq: q.+2 <= n.+1) (ε: side)
    (D: mkprefix) (d: _) :=
    C.(Frame).(restrFrame) (Hpq := ⇓ Hpq) (⇓ Hq) ε d;
|}.

(** The coherence conditions that Frame needs to satisfy to build the next level
   of Frame. These will be used in the proof script of mkFrame. *)

Definition mkLayer {n p} {Hp: p.+1 <= n.+1} {C: NType n} {D: mkprefix}
  {Frame: PartialFrame n.+1 p mkprefix mkFramePrev} {d: Frame.(frame) (↓ Hp) D}: HSet :=
  hforall ε, C.(Filler).(filler) D.2 (Frame.(restrFrame) (Hpq := ♢ _) Hp ε d).

Definition mkRestrLayer {n p q} {ε: side} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n.+1}
  {C: NType n} {D: mkprefix} {Frame: PartialFrame n.+1 p mkprefix mkFramePrev}
  (d: Frame.(frame) (↓ ↓ (Hpq ↕ Hq)) D)
  (l: mkLayer): C.(Layer) (Frame.(restrFrame) Hq ε d) :=
  fun ω => rew [C.(FillerPrev).(filler')] Frame.(cohFrame) d in
    C.(Filler).(restrFiller) (Hpq := ⇓ Hpq) (l ω).

Definition mkCohLayer {n p q r} {ε ω: side} {Hpr: p.+3 <= r.+3}
  {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1} {C: NType n} {D: mkprefix}
  {Frame: PartialFrame n.+1 p mkprefix mkFramePrev}
  {d: Frame.(frame) (↓ ↓ ↓ (Hpr ↕ Hrq ↕ Hq)) D} (l: mkLayer):
  let sl := C.(RestrLayer) (Hpq := ⇓ (Hpr ↕ Hrq)) ε
              (mkRestrLayer (Hpq := ⇓ Hpr) d l) in
  let sl' := C.(RestrLayer) (Hpq := ⇓ Hpr) ω
               (mkRestrLayer (Hpq := ↓ (Hpr ↕ Hrq)) d l) in
  rew [C.(Layer')] Frame.(cohFrame) (Hpr := ↓ Hpr) (Hrq := Hrq) (Hq := Hq) d in sl = sl'.
Proof.
  intros *.
  subst sl sl'; apply functional_extensionality_dep; intros 𝛉; unfold Layer'.
  rewrite <- map_subst_app with
    (P := fun 𝛉 x => C.(FillerPrev).(filler'') (C.(FramePrev).(restrFrame') _ 𝛉 x))
    (f := C.(RestrLayer) _ (mkRestrLayer d l)).
  unfold RestrLayer, mkRestrLayer.
  rewrite <- map_subst with (f := C.(FillerPrev).(restrFiller') (⇓ Hq) ε).
  rewrite <- map_subst with (f := C.(FillerPrev).(restrFiller') (⇓ (Hrq ↕ Hq)) ω).
  rewrite rew_map with
    (P := fun x => (C.(FillerPrev).(filler'') x).(Dom))
    (f := fun x => C.(FramePrev).(restrFrame') (⇓ (Hpr ↕ Hrq) ↕ ⇓ Hq) 𝛉 x).
  rewrite rew_map with
    (P := fun x => (C.(FillerPrev).(filler'') x).(Dom))
    (f := fun x => C.(FramePrev).(restrFrame') (⇓ Hq) ε x).
  rewrite rew_map with
    (P := fun x => (C.(FillerPrev).(filler'') x).(Dom))
    (f := fun x => (C.(FramePrev).(restrFrame') (⇓ (Hrq ↕ Hq)) ω x)).
  rewrite <- (C.(Filler).(cohFiller) (Hrq := ⇓ Hrq) (Hq := ⇓ Hq)).
  repeat rewrite rew_compose.
  apply rew_swap with (P := fun x => (C.(FillerPrev).(filler'') x).(Dom)).
  rewrite rew_app. now reflexivity.
  now apply (C.(FramePrev).(frame'') _ _).(UIP).
Qed.

(* The Frame at level n.+1 with p = O *)
#[local]
Instance mkFrame0 {n} {C: NType n}: PartialFrame n.+1 O mkprefix mkFramePrev.
  unshelve esplit.
  * intros; now exact hunit. (* FrameSn *)
  * simpl; intros; rewrite C.(eqFrame0). now exact tt. (* restrFrameSn *)
  * simpl; intros. (* cohFramep *)
    now rewrite eqRestrFrame0 with (Hpq := ⇓ Hpr),
                eqRestrFrame0 with (Hpq := ⇓ (Hpr ↕ Hrq)).
Defined.

(* The Frame at level n.+1 for S p knowing the Frame at level n.+1 for p *)
#[local]
Instance mkFrameSp {n p} {C: NType n} {Frame: PartialFrame n.+1 p mkprefix mkFramePrev}:
  PartialFrame n.+1 p.+1 mkprefix mkFramePrev.
  unshelve esplit.
  * intros Hp D; exact {d : Frame.(frame) (↓ Hp) D & mkLayer (d := d)}.
  * simpl; intros * ε * (d, l); invert_le Hpq. (* restrFramep *)
    now exact (rew <- [id] C.(eqFrameSp) in
      (Frame.(restrFrame) Hq ε d; mkRestrLayer d l)).
  * simpl; intros q r Hpr Hrq Hq ε ω D (d, l). (* cohframep *)
    invert_le Hpr; invert_le Hrq.

    (* A roundabout way to simplify the proof of mkCohFiller_step *)
    etransitivity. apply (C.(eqRestrFrameSp) (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq)).
    etransitivity.
    2: symmetry; apply (C.(eqRestrFrameSp) (Hpq := ⇓ Hpr) (Hq := ⇓ (Hrq ↕ Hq))).

    apply f_equal with (B := C.(FramePrev).(frame') _ D.1)
      (f := fun x => rew <- (C.(eqFrameSp') (Hp := ⇓ (Hpr ↕ Hrq) ↕ ⇓ Hq)) in x).
    now exact (= Frame.(cohFrame) (Hrq := Hrq) d; mkCohLayer l).
    (* Bug? Coq being too smart for its own good. *)
Defined.

(* Finally, we can define mkFrame at level n.+1 for all p *)
#[local]
Instance mkFrame {n} {C: NType n} p: PartialFrame n.+1 p mkprefix mkFramePrev.
  induction p.
  + now exact mkFrame0. (* p = O *)
  + now exact (mkFrameSp (Frame := IHp)). (* p = S _ *)
Defined.

(** For [Filler], we take a different strategy. We first define [mkfiller],
    [mkRestrFiller], and lemmas corresponding to their computational properties *)

(** First, memoizing the previous levels of [Filler] *)
#[local]
Instance mkFillerPrev {n} {C: NType n} : PartialFillerPrev n.+1 mkprefix mkFramePrev :=
{|
  filler' (p: nat) (Hp: p.+1 <= n.+1) (D: mkprefix) := C.(Filler).(filler) D.2:
    mkFramePrev.(frame') Hp D -> HSet; (* Bug? *)
  filler'' (p: nat) (Hp: p.+2 <= n.+1) (D: mkprefix)
    (d : mkFramePrev.(frame'') Hp D) :=
    C.(FillerPrev).(filler') d;
  restrFiller' (p q: nat) (Hpq: p.+2 <= q.+2) (Hq: q.+2 <= n.+1) (ε: side)
    (D: mkprefix) (d : _) (b : _) := C.(Filler).(restrFiller) (Hpq := ⇓ Hpq)
    (Hq := ⇓ Hq) (E := D.2) b;
|}.

(** Then, the component [filler] of [Filler], built by upwards induction from [p] to [n] *)

Definition mkfiller {n p} {C: NType n} {Hp: p <= n.+1} {D: mkprefix}
  (E: (mkFrame n.+1).(frame) (♢ _) D -> HSet)
  (d: (mkFrame p).(frame) Hp D): HSet.
  revert d; apply le_induction with (Hp := Hp); clear p Hp.
  + now exact E. (* p = n *)
  + intros p Hp mkfillerSp d; exact {l : mkLayer & mkfillerSp (d; l)}. (* p = S n *)
Defined.

Lemma mkfiller_computes {n p} {C: NType n} {Hp: p.+1 <= n.+1} {D: mkprefix}
  {E: (mkFrame n.+1).(frame) (♢ _) D -> HSet} {d}:
  mkfiller (Hp := ↓ Hp) E d = {l : mkLayer & mkfiller (Hp := Hp) E (d; l)} :> Type.
Proof.
  unfold mkfiller; now rewrite le_induction_step_computes.
Qed.

(** Now, [restrFiller], and the corresponding computational properties. *)

Definition mkRestrFiller {n} {C: NType n} {p q} {Hpq: p.+1 <= q.+1}
  {Hq: q.+1 <= n.+1} {ε: side} {D}
  (E: (mkFrame n.+1).(frame) (♢ _) D -> HSet)
  (d: (mkFrame p).(frame) (↓ (Hpq ↕ Hq)) D)
  (Filler: mkfiller (Hp := ↓ (Hpq ↕ Hq)) E d):
    mkFillerPrev.(filler') ((mkFrame p).(restrFrame) Hq ε d).
Proof.
  intros *; revert d Filler; simpl. (* subfillerSn *)
  pattern p, Hpq. (* Bug? Why is this needed? *)
  apply le_induction'.
  + intros d c; rewrite mkfiller_computes in c. destruct c as (l, _).
    now exact (l ε).
  + clear p Hpq; intros p Hpq mkRestrFillerSp d c; invert_le Hpq.
    rewrite mkfiller_computes in c; destruct c as (l, c).
    change (⇓ (↓ ?Hpq ↕ ?Hq)) with (↓ ⇓ (Hpq ↕ Hq)); rewrite C.(eqFillerSp).
    apply mkRestrFillerSp in c.
    now exact (mkRestrLayer d l; c).
Defined.

Lemma mkRestrFiller_base_computes {p n} {C: NType n} {Hp: p.+1 <= n.+1}
  {ε: side} {D E} {d: (mkFrame p).(frame) _ D} {c}:
  mkRestrFiller (Hq := Hp) E d c =
  match (rew [id] mkfiller_computes in c) with
  | (l; _) => l ε
  end.
Proof.
  unfold mkRestrFiller; now rewrite le_induction'_base_computes.
Qed.

Lemma mkRestrFiller_step_computes {q r n} {C: NType n} {Hq: q.+2 <= n.+1}
  {Hrq: r.+2 <= q.+2} {ε: side} {D E} {d: (mkFrame r).(frame) _ D} {c}:
  mkRestrFiller (Hpq := ↓ Hrq) (Hq := Hq) (ε := ε) E d c =
  match (rew [id] mkfiller_computes in c) with
  | (l; c) => rew <- [id] C.(eqFillerSp) in
    (mkRestrLayer d l; mkRestrFiller (Hpq := Hrq) E (d; l) c)
  end.
Proof.
  unfold mkRestrFiller; now rewrite le_induction'_step_computes.
Qed.

(** Now, for the last part of the proof: proving coherence conditions
  on [cohFiller] *)

(* The base case is easily discharged *)
Definition mkCohFiller_base {q r n} {ε ω: side} {C: NType n} {D: mkprefix}
  {Hrq: r.+2 <= q.+2} {Hq: q.+2 <= n.+1}
  {E: (mkFrame n.+1).(frame) (♢ _) D -> HSet}
  (d: (mkFrame r).(frame) (↓ ↓ (Hrq ↕ Hq)) D)
  (c: mkfiller E d):
  rew [mkFillerPrev.(filler'')] (mkFrame r).(cohFrame) (Hpr := ♢ _) d in
    mkFillerPrev.(restrFiller') (Hpq := Hrq) Hq ε
      (mkRestrFiller (ε := ω) (Hpq := ♢ _) (Hq := ↓ (Hrq ↕ Hq)) E d c) =
  mkFillerPrev.(restrFiller') (Hpq := ♢ _) (Hrq ↕ Hq) ω
    (mkRestrFiller (ε := ε) (Hpq := ↓ Hrq) (Hq := Hq) E d c).
  change (♢ _ ↕ ?H) with H; change (⇓ (♢ _) ↕ ?H) with H.
  rewrite mkRestrFiller_base_computes, mkRestrFiller_step_computes.
  destruct (rew [id] mkfiller_computes in c) as (l, c'); clear c.
  now refine (C.(eqRestrFiller0)
    (Q := mkRestrFiller (Hpq := Hrq) E (_; _) c')).
Qed.

(* A small abbreviation *)
Definition mkCohFillerHyp p {q r n} {ε ω: side} {C: NType n} {D: mkprefix}
  (Hpr: p.+2 <= r.+3) {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1}
  {E: (mkFrame n.+1).(frame) (♢ _) D -> HSet}
  (d: (mkFrame p).(frame) (↓ ↓ (Hpr ↕ Hrq ↕ Hq)) D)
  (c: mkfiller E d) :=
  rew [mkFillerPrev.(filler'')] (mkFrame p).(cohFrame) (Hrq := Hrq) d in
  C.(Filler).(restrFiller) (ε := ε) (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq)
    (mkRestrFiller (ε := ω) (Hpq := (⇓ Hpr)) (Hq := ↓ (Hrq ↕ Hq)) E d c) =
  C.(Filler).(restrFiller) (ε := ω) (Hpq := (⇓ Hpr)) (Hq := ⇓ (Hrq ↕ Hq))
    (mkRestrFiller (ε := ε) (Hpq := ↓ (Hpr ↕ Hrq)) (Hq := Hq) E d c).

(* The step case is discharged as (mkCohLayer; IHP) *)
Definition mkCohFiller_step {p q r n} {ε ω: side} {C: NType n} {D: mkprefix}
  {Hpr: p.+3 <= r.+3} {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1}
  {E: (mkFrame n.+1).(frame) (♢ _) D -> HSet}
  {d: (mkFrame p).(frame) (↓ ↓ (↓ Hpr ↕ Hrq ↕ Hq)) D}
  {c: mkfiller E d}
  {IHP: forall (d: (mkFrame p.+1).(frame) (↓ ↓ (Hpr ↕ Hrq ↕ Hq)) D)
        (c: mkfiller E d), mkCohFillerHyp p.+1 Hpr (ε := ε) (ω := ω) d c}:
        mkCohFillerHyp p (↓ Hpr) (ε := ε) (ω := ω) d c.
  unfold mkCohFillerHyp in *; simpl projT1 in *; simpl projT2 in *.
  change (⇓ (↓ ?Hpr)) with (↓ (⇓ Hpr)).
  do 2 rewrite mkRestrFiller_step_computes.
  destruct (rew [id] mkfiller_computes in c) as (l, c'); clear c.
  rewrite (C.(eqRestrFillerSp) (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq)).
  rewrite (C.(eqRestrFillerSp) (Hpq := ⇓ Hpr) (Hq := ⇓ (Hrq ↕ Hq))).
  change ((fun _ (x : leR _ ?y) => x) ↕ ?z) with z.
  change (⇓ ?x ↕ ⇓ ?y) with (⇓ (x ↕ y)).
  rewrite <- rew_permute with (H := @eqFillerSp' _ _ _ (⇓ _) _)
                              (H' := (mkFrame p).(cohFrame) _).
  change (↓ ?Hpr ↕ ?Hrq) with (↓ (Hpr ↕ Hrq)).
  f_equal.
  unshelve eapply (rew_existT_curried (P := C.(Layer'))
  (Q := fun x => C.(FillerPrev).(filler') (rew <- [id] C.(eqFrameSp') in x))
  (H := (mkFrame p).(cohFrame) (Hpr := ↓ Hpr) (Hrq := Hrq) (Hq := Hq) (ε := ε)
        (ω := ω) (D := D) d)
  (u := C.(RestrLayer) (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq) (D := D.1) ε
          (mkRestrLayer (Hpq := ⇓ Hpr) (Hq := ↓ (Hrq ↕ Hq)) (C := C) (D := D)
          (Frame := mkFrame p) (ε := ω) d l))
  (v := rew [C.(FillerPrev).(filler')] C.(eqRestrFrameSp) in
    C.(Filler).(restrFiller) (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq) (ε := ε)
                       (D := D.1) (E := D.2)
                       (mkRestrFiller (Hpq := ⇓ Hpr) (Hq := ↓ (Hrq ↕ Hq))
                       (D := D) (ε := ω) E (d; l) c'))).
  now exact (mkCohLayer (Hpr := Hpr) (Hrq := Hrq) (Hq := Hq) l).
  rewrite <- IHP with (d := (d; l)) (c := c').
  simpl (mkFrame p.+1). unfold mkFillerPrev, filler''.
  change (fun x => C.(FillerPrev).(filler') (Hp := ?Hp) (D := ?D) x) with
    (C.(FillerPrev).(filler') (Hp := Hp) (D := D)).
  unfold mkFrameSp; unfold cohFrame at -1.
  rewrite rew_map with (P := fun x => (C.(FillerPrev).(filler') x).(Dom))
                       (f := fun x => rew <- [id] C.(eqFrameSp') in x).
  repeat rewrite rew_compose.
  set (FEQ := f_equal _ _); simpl in FEQ; clearbody FEQ.
  repeat rewrite <- eq_trans_assoc.
  now rewrite eq_trans_sym_inv_l, eq_trans_refl_r.
Qed.

(** Build a [PartialFiller n.+1] using what we just defined *)
#[local]
Instance mkFiller {n} {C: NType n}:
  PartialFiller n.+1 mkprefix mkFillerPrev mkFrame.
  unshelve esplit; intros p.
  - intros *; now exact mkfiller.
  - intros q Hpq Hq ε d; now exact mkRestrFiller.
  - intros *. revert d c. pattern p, Hpr. apply le_induction''.
    + now exact mkCohFiller_base.
    + clear p Hpr; unfold mkFillerPrev, restrFiller'; cbv beta iota;
      intros p Hpr IHP d c; invert_le Hpr; invert_le Hrq.
      now exact (mkCohFiller_step (IHP := IHP)).
Defined.

(** The base case of a N-parametric set (truncated at dimension 0) *)

#[local]
Instance mkNType0: NType 0.
  unshelve esplit.
  - now exact hunit.
  - unshelve esplit.
    * intros p Hp; now apply leY_contra in Hp.
    * intros p Hp; now apply leY_contra in Hp.
    * intros *; exfalso; now apply leY_contra in Hq.
  - unshelve esplit.
    * intros Hp _; now exact hunit.
    * intros *; exfalso; now apply leY_contra in Hq.
    * intros *; exfalso; clear -Hq; now apply leY_contra in Hq.
  - unshelve esplit; intros *.
    * exfalso; now apply leY_contra in Hp.
    * exfalso; now apply leY_contra in Hp.
    * exfalso; clear -Hq; now apply leY_contra in Hq.
  - unshelve esplit.
    * intros p Hp _ _ _; now exact hunit.
    * simpl; intros *; exfalso; now apply leY_contra in Hq.
    * simpl; intros *; exfalso; now apply leY_contra in Hq.
  - now intros *.
  - intros *; exfalso; now apply leY_contra in len1.
  - intros *; exfalso; now apply leY_contra in Hp.
  - intros *; exfalso; now apply leY_contra in Hp.
  - intros *; exfalso; clear -Hq; now apply leY_contra in Hq.
  - intros *; exfalso; clear -Hp; now apply leY_contra in Hp.
  - intros *; exfalso; clear -Hp; now apply leY_contra in Hp.
  - intros *; exfalso; now apply leY_contra in Hq.
  - intros *; exfalso; clear -Hp; now apply leY_contra in Hp.
  - intros *; exfalso; clear -Hq; now apply leY_contra in Hq.
Defined.

(** We are now ready to build an [NType n.+1] from an [NType n] *)
#[local]
Instance mkNTypeSn {n} {C: NType n}: NType n.+1 :=
{|
    prefix := mkprefix;
    FramePrev := mkFramePrev;
    Frame := mkFrame;
    FillerPrev := mkFillerPrev;
    Filler := mkFiller;
    eqFrame0 := ltac:(now intros *);
    eqFrame0' := ltac:(intros *; now apply C.(eqFrame0));
    eqFrameSp := ltac:(now intros *);
    eqFrameSp' := ltac:(intros *; now refine C.(eqFrameSp));
    eqRestrFrame0 := ltac:(now intros *);
    eqRestrFrameSp := ltac:(now intros *);
    eqFillerSp := ltac:(intros *; simpl; now refine mkfiller_computes);
    eqFillerSp' := ltac:(intros *; now refine C.(eqFillerSp));
    eqRestrFiller0 := ltac:(intros *;
      change (fun _ (_: leR _ ?q) => _) with (♢ q); simpl;
      now rewrite mkRestrFiller_base_computes, rew_rew');
    eqRestrFillerSp := ltac:(intros *; simpl;
      now rewrite mkRestrFiller_step_computes, rew_rew');
|}.

(** An [NType] truncated up to dimension [n] *)
Definition NTypeAt: forall n, NType n.
  induction n.
  - now exact mkNType0.
  - now exact mkNTypeSn.
Defined.

(** The coinductive suffix of an [NType] beyhond level [n] *)
CoInductive NTypeFrom n (X: (NTypeAt n).(prefix)): Type@{m'} := cons {
  this: (NTypeAt n).(Frame).(frame) (♢ n) X -> HSet@{m};
  next: NTypeFrom n.+1 (X; this);
}.

(** The final construction *)
Definition NTypes := NTypeFrom 0 tt.
End NType.

Definition AugmentedSemiSimplicial := NType hunit.
Definition SemiSimplicial := NTypeFrom hunit 1 (tt; fun _ => hunit).
Definition SemiCubical := NType hbool.
