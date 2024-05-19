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

(***********)
(** Frames *)

(** The construction maintains at each step of the induction the three
    last levels of frames (called [frame''], [frame'], [frame]), the
    two restrictions between them (called [restrFrame'] and
    [restrFrame]) and the coherence between these two restrictions
    (called [cohFrame]). *)

(** [FrameBlockPrev] consists of the levels we remember before the
    current one and for each such previous data, [FrameBlock]
    consists of the data to maintain at the current level. *)
Class FrameBlockPrev n (prefix: Type@{m'}) := {
  frame' p {Hp: p.+1 <= n}: prefix -> HSet@{m};
  frame'' p {Hp: p.+2 <= n}: prefix -> HSet@{m};
  restrFrame' p q {Hpq: p.+2 <= q.+2} (Hq: q.+2 <= n) (ε: arity) {D}:
    frame' p D -> frame'' p D;
}.

Arguments frame' {n prefix} _ p {Hp} D.
Arguments frame'' {n prefix} _ p {Hp} D.
Arguments restrFrame' {n prefix} _ p q {Hpq Hq} ε {D} d.

Class FrameBlock n p (prefix: Type@{m'})
  (FramePrev: FrameBlockPrev n prefix) := {
  frame {Hp: p <= n}: prefix -> HSet@{m};
  restrFrame q {Hpq: p.+1 <= q.+1} {Hq: q.+1 <= n} (ε: arity) {D}:
    frame D -> FramePrev.(frame') p D;
  cohFrame r q {Hpr: p.+2 <= r.+2} {Hrq: r.+2 <= q.+2} {Hq: q.+2 <= n}
    {ε ω} {D} (d: frame D):
    FramePrev.(restrFrame') p q ε (restrFrame r ω d) =
    FramePrev.(restrFrame') p r ω (restrFrame q.+1 ε d);
}.

Arguments frame {n} p {prefix FramePrev} _ {Hp} D.
Arguments restrFrame {n} p {prefix FramePrev} _ q {Hpq Hq} ε {D} d.
Arguments cohFrame {n p prefix FramePrev} _ r q {Hpr Hrq Hq ε ω D} d.
(* We want ε and ω to be printed, but have them inferred;
   Coq doesn't support this. *)

(************)
(** Paintings *)

(** We build paintings using an iterated construction: a painting at level n
    depends on paintings at level n-1 and n-2; just as we have frame' and
     frame'', we have painting' and painting''. *)
Class PaintingBlockPrev n (prefix: Type@{m'})
  (FramePrev : FrameBlockPrev n prefix) := {
  painting' {p} {Hp: p.+1 <= n} {D}:
    FramePrev.(frame') p D -> HSet@{m};
  painting'' {p} {Hp: p.+2 <= n} {D}:
    FramePrev.(frame'') p D -> HSet@{m};
  restrPainting' p q {Hpq: p.+2 <= q.+2} (Hq: q.+2 <= n) ε {D}
    {d: FramePrev.(frame') p D}:
    painting' d -> painting'' (FramePrev.(restrFrame') p q ε d);
}.

Arguments painting' {n prefix FramePrev} _ {p Hp D} d.
Arguments painting'' {n prefix FramePrev} _ {p Hp D} d.
Arguments restrPainting' {n prefix FramePrev} _ p q {Hpq Hq} ε {D} [d] b.

(** Painting consists of painting, restrPainting, and coherence conditions between them *)
Class PaintingBlock n (prefix: Type@{m'})
  {FramePrev: FrameBlockPrev n prefix}
  (PaintingPrev: PaintingBlockPrev n prefix FramePrev)
  (Frame: forall {p}, FrameBlock n p prefix FramePrev) := {
  painting {p} {Hp: p <= n} {D}:
    (Frame.(frame n) D -> HSet@{m}) -> Frame.(frame p) D -> HSet@{m};
  restrPainting p q {Hpq: p.+1 <= q.+1} {Hq: q.+1 <= n} ε {D}
    {E: Frame.(frame n) D -> HSet@{m}} {d: Frame.(frame p) D}
    (c: painting E d):
    PaintingPrev.(painting') (Frame.(restrFrame p) q ε d);
  cohPainting p r q {Hpr: p.+2 <= r.+2} {Hrq: r.+2 <= q.+2} {Hq: q.+2 <= n}
    ε ω {D} (E: Frame.(frame n) D -> HSet@{m}) (d: Frame.(frame p) D)
    (c: painting E d):
    rew [PaintingPrev.(painting'')] (Frame.(cohFrame) r q d) in
    PaintingPrev.(restrPainting') p q ε (restrPainting p r ω c) =
      (PaintingPrev.(restrPainting') p r ω (restrPainting p q.+1 ε c));
}.

Arguments painting {n prefix FramePrev PaintingPrev Frame} _ {p Hp D} E.
Arguments restrPainting {n prefix FramePrev PaintingPrev Frame} _ p q
  {Hpq Hq ε D E} [d] c.
Arguments cohPainting {n prefix FramePrev PaintingPrev Frame} _ p r q
  {Hpr Hrq Hq ε ω D E d} c.

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

Class νType n := {
  prefix: Type@{m'};
  FramePrev: FrameBlockPrev n prefix;
  Frame {p}: FrameBlock n p prefix FramePrev;
  PaintingPrev: PaintingBlockPrev n prefix FramePrev;
  Painting: PaintingBlock n prefix PaintingPrev (@Frame);

  (** Abbreviations for [ν]-family of previous paintings, one for
      each [ϵ]-restriction of the previous frame (ϵ∈ν) *)
  Layer {p} {Hp: p.+1 <= n} {D} (d: Frame.(frame p) D) :=
    hforall ε, PaintingPrev.(painting') (Frame.(restrFrame p) p ε d);
  Layer' {p} {Hp: p.+2 <= n} {D} (d: FramePrev.(frame') p D) :=
    hforall ε, PaintingPrev.(painting'') (FramePrev.(restrFrame') p p ε d);
  RestrLayer {p q} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n} ε {D}
    {d: Frame.(frame p) D}:
    Layer d -> Layer' (Frame.(restrFrame p) q.+1 ε d) :=
  fun l ω => rew [PaintingPrev.(painting'')] Frame.(cohFrame) p q d in
    PaintingPrev.(restrPainting') p q ε (l ω);

  (** Equations carrying the definition of frame and painting from level
      [n]-1 and [n]-2 *)
  eqFrame0 {len0: 0 <= n} {D}: (Frame.(frame 0) D).(Dom) = unit;
  eqFrame0' {len1: 1 <= n} {D}: (FramePrev.(frame') 0 D).(Dom) = unit;
  eqFrameSp {p} {Hp: p.+1 <= n} {D}:
    Frame.(frame p.+1) D = {d: Frame.(frame p) D & Layer d} :> Type;
  eqFrameSp' {p} {Hp: p.+2 <= n} {D}:
    FramePrev.(frame') p.+1 D = {d: FramePrev.(frame') p D & Layer' d}
      :> Type;
  eqRestrFrame0 {q} {Hpq: 1 <= q.+1} {Hq: q.+1 <= n} {ε} {D}:
    Frame.(restrFrame O) q ε (rew <- [id] eqFrame0 (D := D) in tt) =
      rew <- [id] eqFrame0' in tt;
  eqRestrFrameSp {ε p q} {D} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n}
    {d: Frame.(frame p) D} {l: Layer d}:
    Frame.(restrFrame p.+1) q.+1 ε (rew <- [id] eqFrameSp in (d; l)) =
      rew <- [id] eqFrameSp' in (Frame.(restrFrame _) _ ε d; RestrLayer ε l);
  eqPaintingSp {p} {Hp: p.+1 <= n} {D E d}:
    Painting.(painting) (p := p) E d = {l: Layer d &
      Painting.(painting) (D := D) E (rew <- [id] eqFrameSp in (d; l))}
        :> Type;
  eqPaintingSp' {p} {Hp: p.+2 <= n} {D d}:
    PaintingPrev.(painting') (p := p) d = {b : Layer' d &
      PaintingPrev.(painting') (rew <- [id] eqFrameSp' (D := D) in (d; b))}
        :> Type;
  eqRestrPainting0 {p} {Hp: p.+1 <= n} {ε} {D E d} {l: Layer d}
    (Q: Painting.(painting) (D := D) E (rew <- eqFrameSp in (d; l))):
    l ε = Painting.(restrPainting) p p
      (rew <- [id] eqPaintingSp in (l; Q));
  eqRestrPaintingSp p q {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n} {ε} {D E d}
    {l: Layer d}
    {Q: Painting.(painting) (D := D) E (rew <- eqFrameSp in (d; l))}:
    Painting.(restrPainting) p q.+1 (ε := ε)
      (rew <- [id] eqPaintingSp in (l; Q)) =
    rew <- [id] eqPaintingSp' in
      (RestrLayer ε l; rew [PaintingPrev.(painting')] eqRestrFrameSp in
        Painting.(restrPainting) p.+1 q.+1 Q);
}.

Arguments prefix {n} _.
Arguments FramePrev {n} _.
Arguments PaintingPrev {n} _.
Arguments Frame {n} _ {p}.
Arguments Painting {n} _.
Arguments Layer {n} _ {p Hp D} d.
Arguments Layer' {n} _ {p Hp D} d.
Arguments RestrLayer {n} _ {p q Hpq Hq} ε {D d} l.
Arguments eqFrame0 {n} _ {len0 D}.
Arguments eqFrame0' {n} _ {len1 D}.
Arguments eqFrameSp {n} _ {p Hp D}.
Arguments eqFrameSp' {n} _ {p Hp D}.
Arguments eqRestrFrame0 {n} _ {q Hpq Hq ε D}.
Arguments eqRestrFrameSp {n} _ {ε p q D Hpq Hq d l}.
Arguments eqPaintingSp {n} _ {p Hp D E d}.
Arguments eqPaintingSp' {n} _ {p Hp D d}.
Arguments eqRestrPainting0 {n} _ {p Hp ε D E d l} Q.
Arguments eqRestrPaintingSp {n} _ p q {Hpq Hq ε D E d l Q}.

(***************************************************)
(** The construction of [νType n+1] from [νType n] *)

(** Extending the initial prefix *)
Definition mkprefix {n} {C: νType n}: Type@{m'} :=
  sigT (fun D : C.(prefix) => C.(Frame).(frame n) D -> HSet@{m}).

(** Memoizing the previous levels of [Frame] *)
Definition mkFramePrev {n} {C: νType n}: FrameBlockPrev n.+1 mkprefix := {|
  frame' p (Hp: p.+1 <= n.+1) D := C.(Frame).(frame p) D.1;
  frame'' p (Hp: p.+2 <= n.+1) D := C.(FramePrev).(frame') p D.1;
  restrFrame' p q (Hpq: p.+2 <= q.+2) (Hq: q.+2 <= n.+1) ε D d :=
    C.(Frame).(restrFrame p) q ε d;
|}.

(** The coherence conditions that Frame needs to satisfy to build the next level
   of Frame. These will be used in the proof script of mkFrame. *)

Definition mkLayer {n} {C: νType n} {p} {Hp: p.+1 <= n.+1}
  {Frame: FrameBlock n.+1 p mkprefix mkFramePrev}
  {D} {d: Frame.(frame p) D}: HSet :=
  hforall ε, C.(Painting).(painting) D.2
    (Frame.(restrFrame p) p ε d).

Definition mkLayer' {n} {C: νType n} {p} {Hp: p.+2 <= n.+1}
  {D} {d: mkFramePrev.(frame' (n := n.+1)) p D}: HSet := C.(Layer) d.

Definition mkRestrLayer {n} {C: νType n} {p q} {Hpq: p.+2 <= q.+2}
  {Hq: q.+2 <= n.+1} {ε} {Frame: FrameBlock n.+1 p mkprefix mkFramePrev}
  {D} {d: Frame.(frame p) D}: mkLayer -> mkLayer' :=
  fun l ω => rew [C.(PaintingPrev).(painting')] Frame.(cohFrame) p q d in
    C.(Painting).(restrPainting) p q (ε := ε) (l ω).

Definition mkCohLayer {n} {C: νType n} {p q r} {Hpr: p.+3 <= r.+3}
  {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1} {ε ω}
  {Frame: FrameBlock n.+1 p mkprefix mkFramePrev}
  {D} {d: Frame.(frame p) D} (l: mkLayer):
  let sl := C.(RestrLayer) (Hpq := ⇓ (Hpr ↕ Hrq)) ε
              (mkRestrLayer (p := p) (q := r) l) in
  let sl' := C.(RestrLayer) (Hpq := ⇓ Hpr) ω
               (mkRestrLayer (p := p) (q := q.+1) l) in
  rew [C.(Layer')] Frame.(cohFrame) r.+1 q.+1 d in sl = sl'.
Proof.
  intros *.
  subst sl sl'; apply functional_extensionality_dep; intros 𝛉; unfold Layer'.
  rewrite <- map_subst_app with
    (P := fun 𝛉 x => C.(PaintingPrev).(painting'')
      (C.(FramePrev).(restrFrame') _ _ 𝛉 x))
    (f := C.(RestrLayer) _ (mkRestrLayer l)).
  unfold RestrLayer, mkRestrLayer.
  rewrite <- map_subst with (f := C.(PaintingPrev).(restrPainting') p q ε).
  rewrite <- map_subst with
    (f := C.(PaintingPrev).(restrPainting') p r ω).
  rewrite rew_map with
    (P := fun x => (C.(PaintingPrev).(painting'') x).(Dom))
    (f := fun x => C.(FramePrev).(restrFrame') _ _ 𝛉 x).
  rewrite rew_map with
    (P := fun x => (C.(PaintingPrev).(painting'') x).(Dom))
    (f := fun x => C.(FramePrev).(restrFrame') _ _ ε x).
  rewrite rew_map with
    (P := fun x => (C.(PaintingPrev).(painting'') x).(Dom))
    (f := fun x => (C.(FramePrev).(restrFrame') _ _ ω x)).
  rewrite <- (C.(Painting).(cohPainting) p r q).
  repeat rewrite rew_compose.
  apply rew_swap with (P := fun x => (C.(PaintingPrev).(painting'') x).(Dom)).
  rewrite rew_app. now reflexivity.
  now apply (C.(FramePrev).(frame'') p _).(UIP).
Qed.

(** The Frame at level n.+1 with p = O *)
#[local]
Instance mkFrame0 {n} {C: νType n}: FrameBlock n.+1 O mkprefix mkFramePrev.
  unshelve esplit.
  * intros; now exact hunit. (* FrameSn *)
  * simpl; intros; rewrite C.(eqFrame0); now exact tt. (* restrFrameSn *)
  * simpl; intros. (* cohFramep *)
    now rewrite eqRestrFrame0 with (q := r),
                eqRestrFrame0 with (q := q).
Defined.

(** The Frame at level n.+1 for p.+1 knowing the Frame at level n.+1 for p *)
#[local]
Instance mkFrameSp {n} {C: νType n} {p}
  {Frame: FrameBlock n.+1 p mkprefix mkFramePrev}:
  FrameBlock n.+1 p.+1 mkprefix mkFramePrev.
  unshelve esplit.
  * intros Hp D; exact {d : Frame.(frame p) D & mkLayer (d := d)}.
  * simpl; intros * ε * (d, l); invert_le Hpq. (* restrFramep *)
    now exact (rew <- [id] C.(eqFrameSp) in
      (Frame.(restrFrame _) _ ε d; mkRestrLayer l)).
  * simpl; intros q r Hpr Hrq Hq ε ω D (d, l). (* cohframep *)
    invert_le Hpr; invert_le Hrq.

    (* A roundabout way to simplify the proof of mkCohPainting_step *)
    etransitivity.
    apply (C.(eqRestrFrameSp) (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq)).
    etransitivity.
    2: symmetry; apply (C.(eqRestrFrameSp) (Hpq := ⇓ Hpr) (Hq := ⇓ (Hrq ↕ Hq))).

    apply f_equal with (B := C.(FramePrev).(frame') _ D.1)
      (f := fun x => rew <- (C.(eqFrameSp') (p := p)) in x).
    now exact (= Frame.(cohFrame) q.+1 r.+1 d; mkCohLayer l).
Defined.

(** Finally, we can define mkFrame at level n.+1 for all p *)
#[local]
Instance mkFrame {n} {C: νType n} p: FrameBlock n.+1 p mkprefix mkFramePrev.
  induction p.
  * now exact mkFrame0. (* p = O *)
  * now exact mkFrameSp. (* p = S _ *)
Defined.

(** For [Painting], we take a different strategy. We first define [mkpainting],
    [mkRestrPainting], and lemmas corresponding to their computational properties *)

(** First, memoizing the previous levels of [Painting] *)
#[local]
Instance mkPaintingPrev {n} {C: νType n}:
  PaintingBlockPrev n.+1 mkprefix mkFramePrev :=
{|
  painting' p (Hp: p.+1 <= n.+1) D := C.(Painting).(painting) D.2:
    mkFramePrev.(frame') p D -> HSet; (* Coq bug? *)
  painting'' p (Hp: p.+2 <= n.+1) D (d: mkFramePrev.(frame'') p D) :=
    C.(PaintingPrev).(painting') d;
  restrPainting' p q (Hpq: p.+2 <= q.+2) (Hq: q.+2 <= n.+1) (ε: arity) D d b :=
    C.(Painting).(restrPainting) p q (E := D.2) b;
|}.

(** Then, the component [painting] of [Painting], built by upwards induction from [p] to [n] *)

Definition mkpainting {n} {C: νType n} {p} {Hp: p <= n.+1} {D}
  (E: (mkFrame n.+1).(frame n.+1) D -> HSet)
  (d: (mkFrame p).(frame p) D): HSet.
Proof.
  revert d; apply le_induction with (Hp := Hp); clear p Hp.
  * now exact E. (* p = n *)
  * intros p Hp mkpaintingSp d. (* p = S n *)
    now exact {l : mkLayer & mkpaintingSp (d; l)}.
Defined.

Lemma mkpainting_computes {n p} {C: νType n} {Hp: p.+1 <= n.+1} {D}
  {E: (mkFrame n.+1).(frame n.+1) D -> HSet} {d}:
  mkpainting (Hp := ↓ Hp) E d =
  {l : mkLayer & mkpainting (Hp := Hp) E (d; l)} :> Type.
Proof.
  unfold mkpainting; now rewrite le_induction_step_computes.
Qed.

(** Now, [restrPainting], and the corresponding computational properties. *)

Definition mkRestrPainting {n} {C: νType n} p q {Hpq: p.+1 <= q.+1}
  {Hq: q.+1 <= n.+1} {ε} {D}
  (E: (mkFrame n.+1).(frame n.+1) D -> HSet)
  (d: (mkFrame p).(frame p) D)
  (Painting: mkpainting (Hp := ↓ (Hpq ↕ Hq)) E d):
    mkPaintingPrev.(painting') ((mkFrame p).(restrFrame p) q ε d).
Proof.
  intros *; revert d Painting; simpl.
  pattern p, Hpq. (* Bug? Why is this needed? *)
  apply le_induction'.
  * intros d c; rewrite mkpainting_computes in c. destruct c as (l, _).
    now exact (l ε).
  * clear p Hpq; intros p Hpq mkRestrPaintingSp d c; invert_le Hpq.
    rewrite mkpainting_computes in c; destruct c as (l, c).
    rewrite C.(eqPaintingSp).
    apply mkRestrPaintingSp in c.
    now exact (mkRestrLayer l; c).
Defined.

Lemma mkRestrPainting_base_computes {n} {C: νType n} {p} {Hp: p.+1 <= n.+1}
  {ε} {D E} {d: (mkFrame p).(frame p) D} {c}:
  mkRestrPainting p p E d c =
  match (rew [id] mkpainting_computes in c) with
  | (l; _) => l ε
  end.
Proof.
  unfold mkRestrPainting; now rewrite le_induction'_base_computes.
Qed.

Lemma mkRestrPainting_step_computes {n} {C: νType n} {q r} {Hrq: r.+2 <= q.+2}
  {Hq: q.+2 <= n.+1} {ε} {D E} {d: (mkFrame r).(frame r) D} {c}:
  mkRestrPainting r q.+1 (Hpq := ↓ Hrq) (Hq := Hq) (ε := ε) E d c =
  match (rew [id] mkpainting_computes in c) with
  | (l; c) => rew <- [id] C.(eqPaintingSp) in
    (mkRestrLayer l; mkRestrPainting r.+1 q.+1 E (d; l) c)
  end.
Proof.
  unfold mkRestrPainting; now rewrite le_induction'_step_computes.
Qed.

(** Now, for the last part of the proof: proving coherence conditions
    on [cohPainting] *)

(** The base case is easily discharged *)
Definition mkCohPainting_base {n} {C: νType n} {q r}
  {Hrq: r.+2 <= q.+2} {Hq: q.+2 <= n.+1} {ε ω}
  {D} {E: (mkFrame n.+1).(frame n.+1) D -> HSet}
  (d: (mkFrame r).(frame r) D)
  (c: mkpainting E d):
  rew [mkPaintingPrev.(painting'')] (mkFrame r).(cohFrame) r q d in
    mkPaintingPrev.(restrPainting') r q ε
      (mkRestrPainting r r (ε := ω) E d c) =
  mkPaintingPrev.(restrPainting') r r ω
    (mkRestrPainting r q.+1 (ε := ε) E d c).
Proof.
  rewrite mkRestrPainting_base_computes, mkRestrPainting_step_computes.
  destruct (rew [id] mkpainting_computes in c) as (l, c'); clear c.
  now refine (C.(eqRestrPainting0) (mkRestrPainting r.+1 q.+1 E (_; _) c')).
Qed.

(** A small abbreviation *)
Definition mkCohPaintingHyp {n} {C: νType n}
  p {q r} (Hpr: p.+2 <= r.+3) {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1}
  {ε ω} {D} {E: (mkFrame n.+1).(frame n.+1) D -> HSet}
  (d: (mkFrame p).(frame p) D)
  (c: mkpainting E d) :=
  rew [mkPaintingPrev.(painting'')] (mkFrame p).(cohFrame) r.+1 q.+1 d in
  C.(Painting).(restrPainting) p q.+1 (ε := ε)
    (mkRestrPainting p r.+1 E d c) =
  C.(Painting).(restrPainting) p r.+1 (ε := ω)
    (mkRestrPainting p q.+2 (ε := ε) E d c).

(** The step case is discharged as (mkCohLayer; IHP) *)
Definition mkCohPainting_step {n} {C: νType n} {p q r} {Hpr: p.+3 <= r.+3}
  {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1} {ε ω}
  {D} {E: (mkFrame n.+1).(frame n.+1) D -> HSet}
  {d: (mkFrame p).(frame p) D}
  {c: mkpainting E d}
  {IHP: forall (d: (mkFrame p.+1).(frame p.+1) D)
        (c: mkpainting E d), mkCohPaintingHyp p.+1 Hpr (ε := ε) (ω := ω) d c}:
        mkCohPaintingHyp p (↓ Hpr) (ε := ε) (ω := ω) d c.
Proof.
  unfold mkCohPaintingHyp in *; simpl projT1 in *; simpl projT2 in *.
  do 2 rewrite mkRestrPainting_step_computes.
  destruct (rew [id] mkpainting_computes in c) as (l, c'); clear c.
  rewrite (C.(eqRestrPaintingSp) p q),
          (C.(eqRestrPaintingSp) p r).
  rewrite <- rew_permute with (H := @eqPaintingSp' _ _ _ (⇓ _) _)
                              (H' := (mkFrame p).(cohFrame) r.+1 q.+1 d).
  f_equal.
  unshelve eapply (rew_existT_curried (P := C.(Layer'))
  (Q := fun x => C.(PaintingPrev).(painting') (rew <- [id] C.(eqFrameSp') in x))
  (H := (mkFrame p).(cohFrame) r.+1 q.+1 (ε := ε) (ω := ω) (D := D) d)
  (u := C.(RestrLayer) (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq) (D := D.1) ε
          (mkRestrLayer (p := p) (q := r) (C := C) (D := D)
          (Frame := mkFrame p) (ε := ω) l))
  (v := rew [C.(PaintingPrev).(painting')] C.(eqRestrFrameSp) in
    C.(Painting).(restrPainting) p.+1 q.+1 (ε := ε)
                       (D := D.1) (E := D.2)
                       (mkRestrPainting p.+1 r.+1
                       (D := D) (ε := ω) E (d; l) c'))).
  now exact (mkCohLayer (Hpr := Hpr) (Hrq := Hrq) (Hq := Hq) l).
  rewrite <- IHP with (d := (d; l)) (c := c').
  simpl (mkFrame p.+1). unfold mkPaintingPrev, painting''.
  unfold mkFrameSp, cohFrame.
  rewrite rew_map with (P := fun x => (C.(PaintingPrev).(painting') x).(Dom))
                       (f := fun x => rew <- [id] C.(eqFrameSp') in x).
  repeat rewrite rew_compose.
  set (FEQ := f_equal _ _); simpl in FEQ; clearbody FEQ.
  repeat rewrite <- eq_trans_assoc.
  now rewrite eq_trans_sym_inv_l, eq_trans_refl_r.
Qed.

(** Build a [PaintingBlock n.+1] using what we just defined *)
#[local]
Instance mkPainting {n} {C: νType n}:
  PaintingBlock n.+1 mkprefix mkPaintingPrev mkFrame.
  unshelve esplit; intros p.
  * intros *; now exact mkpainting.
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
    * intros p Hp D E d. now exact (E d).
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

(** We are now ready to build an [νType n.+1] from an [νType n] *)
#[local]
Instance mkνTypeSn {n} (C: νType n): νType n.+1 :=
{|
    prefix := mkprefix;
    FramePrev := mkFramePrev;
    Frame := mkFrame;
    PaintingPrev := mkPaintingPrev;
    Painting := mkPainting;
    eqFrame0 := ltac:(now intros *);
    eqFrame0' := ltac:(intros *; now apply C.(eqFrame0));
    eqFrameSp := ltac:(now intros *);
    eqFrameSp' := ltac:(intros *; now refine C.(eqFrameSp));
    eqRestrFrame0 := ltac:(now intros *);
    eqRestrFrameSp := ltac:(now intros *);
    eqPaintingSp := ltac:(intros *; now refine mkpainting_computes);
    eqPaintingSp' := ltac:(intros *; now refine C.(eqPaintingSp));
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
  this: (νTypeAt n).(Frame).(frame n) X -> HSet@{m};
  next: νTypeFrom n.+1 (X; this);
}.

(** The final construction *)
Definition νTypes := νTypeFrom 0 tt.

(* Degeneracies *)

Class DgnFrameBlockPrev {n'} (C: νType n'.+1) := {
  dgnFrame' {p} (Hp: p.+2 <= n'.+1) {D}:
    C.(FramePrev).(frame'') p D -> C.(FramePrev).(frame') p D;
}.

Arguments dgnFrame' {n' C} _ {p} Hp {D} d.

Class DgnFrameBlock {n'} (C: νType n'.+1) p (Prev: DgnFrameBlockPrev C) := {
  dgnFrame (Hp: p.+1 <= n'.+1) {D}:
    C.(FramePrev).(frame') p D -> C.(Frame).(frame p) D;
  idDgnRestrFrame {ε} {Hp: p.+1 <= n'.+1} {D}
    {d: C.(FramePrev).(frame') p D}:
    C.(Frame).(restrFrame p) n' ε
      (dgnFrame Hp d) = d;
  cohDgnRestrFrame {q ε} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n'.+1} {D}
    {d: C.(FramePrev).(frame') p D}:
    Prev.(dgnFrame') (Hpq ↕ Hq)
    (C.(FramePrev).(restrFrame') p q ε d) =
      C.(Frame).(restrFrame p) q ε
        (dgnFrame (↓ (Hpq ↕ Hq)) d);
}.

Arguments dgnFrame {n' C p Prev} _ Hp {D} d.
Arguments idDgnRestrFrame {n' C p Prev} _ {ε Hp D d}.
Arguments cohDgnRestrFrame {n' C p Prev} _ {q ε Hpq Hq D d}.

Class DgnPaintingBlockPrev {n'} (C: νType n'.+1) (Prev: DgnFrameBlockPrev C) := {
  dgnPainting' {p} (Hp: p.+2 <= n'.+1) {D} {d: C.(FramePrev).(frame'') p D}:
    C.(PaintingPrev).(painting'') d ->
    C.(PaintingPrev).(painting') (Prev.(dgnFrame') Hp d);
}.

Arguments dgnPainting' {n' C Prev} _ {p} Hp {D d} c.

Class DgnPaintingBlock {n'} (C: νType n'.+1) {Q: DgnFrameBlockPrev C}
  (Prev: DgnPaintingBlockPrev C Q)
  (FrameBlock: forall {p}, DgnFrameBlock C p Q) := {
  dgnPainting {p} (Hp: p.+1 <= n'.+1) {D E} {d: C.(FramePrev).(frame') p D}:
    C.(PaintingPrev).(painting') d ->
    C.(Painting).(painting) E (FrameBlock.(dgnFrame) Hp d);
  idDgnRestrPainting {p ε} {Hp: p.+1 <= n'.+1} {D E}
    {d: C.(FramePrev).(frame') p D}
    {c: C.(PaintingPrev).(painting') d}:
    rew [C.(PaintingPrev).(painting')] FrameBlock.(idDgnRestrFrame) in
    C.(Painting).(restrPainting) p n' (ε := ε) (E := E)
      (dgnPainting Hp c) = c;
}.

Arguments dgnPainting {n' C Q Prev FrameBlock} _ {p} Hp {D E d} c.
Arguments idDgnRestrPainting {n' C Q Prev FrameBlock} _ {p ε Hp D E d c}.

Class Dgn {n'} (C: νType n'.+1) := {
  DgnFramePrev: DgnFrameBlockPrev C;
  DgnFrame {p}: DgnFrameBlock C p DgnFramePrev;
  DgnPaintingPrev: DgnPaintingBlockPrev C DgnFramePrev;
  DgnPainting: DgnPaintingBlock C DgnPaintingPrev (@DgnFrame);

  DgnLayer {p} {Hp: p.+2 <= n'.+1} {D} (d: C.(FramePrev).(frame') p D):
    C.(Layer') d -> C.(Layer) (DgnFrame.(dgnFrame) (↓ Hp) d) :=
    fun l ω => rew [C.(PaintingPrev).(painting')]
    DgnFrame.(cohDgnRestrFrame) in DgnPaintingPrev.(dgnPainting') Hp (l ω);
}.

Arguments DgnFramePrev {n' C} _.
Arguments DgnFrame {n' C} _ {p}.
Arguments DgnPaintingPrev {n' C} _.
Arguments DgnPainting {n' C} _.
Arguments DgnLayer {n' C} _ {p Hp D d} l.

#[local]
Instance mkDgnFramePrev {n'} {G: Dgn (νTypeAt n'.+1)}:
  DgnFrameBlockPrev (νTypeAt n'.+2) := {|
  dgnFrame' p Hp (D: (νTypeAt n'.+2).(prefix)) d :=
    G.(DgnFrame).(dgnFrame) (⇓ Hp) d;
|}.

Definition mkDgnLayer {n' p} {G: Dgn (νTypeAt n'.+1)}
  {Hp: p.+2 <= n'.+2} {Frame: DgnFrameBlock (νTypeAt n'.+2) p mkDgnFramePrev}
  {D} {d: mkFramePrev.(frame') p D}:
  mkLayer' (d := d) -> mkLayer (d := Frame.(dgnFrame) (↓ Hp) d) :=
  fun l ω => rew [(νTypeAt n'.+1).(Painting).(painting) D.2]
    Frame.(cohDgnRestrFrame) in G.(DgnPainting).(dgnPainting) (⇓ Hp) (l ω).

Definition mkidDgnRestrLayer {n' p ε} {G: Dgn (νTypeAt n'.+1)}
  {Hp: p.+2 <= n'.+2}
  {FrameBlock: DgnFrameBlock (νTypeAt n'.+2) p mkDgnFramePrev} {D}
  {d: mkFramePrev.(frame') p D} {l: mkLayer' (d := d)}:
  rew [fun d => mkLayer' (d := d)]
    FrameBlock.(idDgnRestrFrame) (ε := ε) in
      mkRestrLayer (p := p) (q := n') (mkDgnLayer l) = l.
Proof.
  apply functional_extensionality_dep; intros 𝛉.
  rewrite <-
    (G.(DgnPainting).(idDgnRestrPainting) (ε := ε) (E := D.2) (c := l 𝛉)).
  unfold mkRestrLayer, mkDgnLayer; rewrite <- map_subst_app; fold (νTypeAt n').
  repeat rewrite <- map_subst.
  rewrite rew_map with
    (P := fun x => (mkνTypeSn (νTypeAt n')).(PaintingPrev).(painting') x).
  rewrite rew_map with
    (P := fun x => (mkνTypeSn (νTypeAt n')).(PaintingPrev).(painting') x)
    (f := fun d => (mkνTypeSn (νTypeAt n')).(Frame).(restrFrame _) n' ε d).
  repeat rewrite rew_compose.
  apply rew_swap with
    (P := fun x => (mkνTypeSn (νTypeAt n')).(PaintingPrev).(painting') x).
  rewrite rew_app. now trivial.
  now apply ((mkνTypeSn (νTypeAt n')).(FramePrev).(frame') p D.1).(UIP).
Defined.

#[local]
Instance mkDgnFrame0 {n'} {G: Dgn (νTypeAt n'.+1)}:
  DgnFrameBlock (νTypeAt n'.+2) O mkDgnFramePrev.
  unshelve esplit.
  * intros; now exact tt.
  * intros; apply rew_swap with (P := id); now destruct (rew <- _ in _).
  * intros; apply rew_swap with (P := id); now destruct (rew _ in _).
Defined.

#[local]
Instance mkDgnFrameSp {n' p} {G: Dgn (νTypeAt n'.+1)}
  {Frame: DgnFrameBlock (νTypeAt n'.+2) p mkDgnFramePrev}:
  DgnFrameBlock (νTypeAt n'.+2) p.+1 mkDgnFramePrev.
  unshelve esplit.
  * (* dgnFrame *)
    intros Hp D (d, l).
    now exact (Frame.(dgnFrame) _ d; mkDgnLayer l).
  * (* idDgnRestrFrame *)
    simpl; intros ε Hp D (d, l).
    now exact (= Frame.(idDgnRestrFrame); mkidDgnRestrLayer).
  * (* cohDgnRestrFrame *)
    simpl; intros q ε Hpq Hq D (d, l). invert_le Hpq. invert_le Hq.
    symmetry.
    exact (= Frame.(idDgnRestrFrame); mkidDgnRestrLayer).
    admit.
Admitted.

#[local]
Instance mkDgnFrameBlock {n' p} {G: Dgn (νTypeAt n'.+1)}:
  DgnFrameBlock (νTypeAt n'.+2) p mkDgnFramePrev.
  induction p.
  * now exact mkDgnFrame0.
  * now exact mkDgnFrameSp.
Defined.

End νType.

Definition AugmentedSemiSimplicial := νTypes hunit.
Definition SemiSimplicial := νTypeFrom hunit 1 (tt; fun _ => hunit).
Definition SemiCubical := νTypes hbool.

(** Some examples *)

Notation "{ x : A && P }" := (sigT (A := A) (fun x => P)): type_scope.

Example SemiSimplicial2 := Eval lazy -[projT2] in
 (νTypeAt hunit 2).(prefix _).
Print SemiSimplicial2.

Example SemiCubical2 := Eval lazy -[projT2] in
 (νTypeAt hbool 2).(prefix _).
Print SemiCubical2.
