(** An "indexed" construction of ν-parametric sets
    For ν=1, this builds augmented semi-simplicial sets
    For ν=2, this builds semi-cubical sets *)

Import Logic.EqNotations.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Arith.Peano_dec.
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
Arguments restrFrame {n p prefix FramePrev} _ q {Hpq Hq} ε {D} d.
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
    PaintingPrev.(painting') (Frame.(restrFrame) q ε d);
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
    hforall ε, PaintingPrev.(painting') (Frame.(restrFrame) p ε d);
  Layer' {p} {Hp: p.+2 <= n} {D} (d: FramePrev.(frame') p D) :=
    hforall ε, PaintingPrev.(painting'') (FramePrev.(restrFrame') p p ε d);
  RestrLayer {p q} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n} ε {D}
    {d: Frame.(frame p) D}:
    Layer d -> Layer' (Frame.(restrFrame) q.+1 ε d) :=
  fun l ω => rew [PaintingPrev.(painting'')] Frame.(cohFrame) p q d in
    PaintingPrev.(restrPainting') p q ε (l ω);

  (** Equations carrying the definition of frame and painting from level
      [n]-1 and [n]-2 *)
  eqFrame0 {len0: 0 <= n} {D}: Frame.(frame 0) D = hunit :> Type;
  eqFrame0' {len1: 1 <= n} {D}: FramePrev.(frame') 0 D = hunit :> Type;
  eqFrameSp {p} {Hp: p.+1 <= n} {D}:
    Frame.(frame p.+1) D = {d: Frame.(frame p) D & Layer d} :> Type;
  eqFrameSp' {p} {Hp: p.+2 <= n} {D}:
    FramePrev.(frame') p.+1 D = {d: FramePrev.(frame') p D & Layer' d}
      :> Type;
  eqRestrFrame0 {q} {Hpq: 1 <= q.+1} {Hq: q.+1 <= n} {ε} {D}:
    Frame.(restrFrame (p:=0)) q ε (rew <- [id] eqFrame0 (D := D) in tt) =
      rew <- [id] eqFrame0' in tt;
  eqRestrFrameSp {ε p q} {D} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n}
    {d: Frame.(frame p) D} {l: Layer d}:
    Frame.(restrFrame (p:=p.+1)) q.+1 ε (rew <- [id] eqFrameSp in (d; l)) =
      rew <- [id] eqFrameSp' in (Frame.(restrFrame) q.+1 ε d; RestrLayer ε l);
  eqPainting0 {D E d}:
   Painting.(painting) (p := n) (D := D) E d = E d :> Type;
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
  eqRestrPainting0' {p} {Hp : p.+2 <= n} {ε : arity} {D d}
    {l : (Layer') d}
    {Q : (PaintingPrev) .(painting') (D := D) (rew <- [id] eqFrameSp' in (d; l))} :
    l ε = (PaintingPrev) .(restrPainting') p p ε
      (rew <- [id] (eqPaintingSp') in (l ; Q));
}.

Arguments prefix {n} _.
Arguments FramePrev {n} _.
Arguments PaintingPrev {n} _.
Arguments Frame {n} _ {p}.
Arguments Painting {n} _.
Arguments Layer {n} _ {p Hp D} d.
Arguments Layer' {n} _ {p Hp D} d.
Arguments RestrLayer {n} _ p q {Hpq Hq} ε {D d} l.
Arguments eqFrame0 {n} _ {len0 D}.
Arguments eqFrame0' {n} _ {len1 D}.
Arguments eqFrameSp {n} _ {p Hp D}.
Arguments eqFrameSp' {n} _ {p Hp D}.
Arguments eqRestrFrame0 {n} _ {q Hpq Hq ε D}.
Arguments eqRestrFrameSp {n} _ {ε p q D Hpq Hq d l}.
Arguments eqPainting0 {n} _ {D E d}.
Arguments eqPaintingSp {n} _ {p Hp D E d}.
Arguments eqPaintingSp' {n} _ {p Hp D d}.
Arguments eqRestrPainting0 {n} _ {p Hp ε D E d l} Q.
Arguments eqRestrPaintingSp {n} _ p q {Hpq Hq ε D E d l Q}.

(***************************************************)
(** The construction of [νType n+1] from [νType n] *)

(** Extending the initial prefix *)
Definition mkPrefix {n} {C: νType n}: Type@{m'} :=
  sigT (fun D : C.(prefix) => C.(Frame).(frame n) D -> HSet@{m}).

(** Memoizing the previous levels of [Frame] *)
Definition mkFramePrev {n} {C: νType n}: FrameBlockPrev n.+1 mkPrefix := {|
  frame' p (Hp: p.+1 <= n.+1) D := C.(Frame).(frame p) D.1;
  frame'' p (Hp: p.+2 <= n.+1) D := C.(FramePrev).(frame') p D.1;
  restrFrame' p q (Hpq: p.+2 <= q.+2) (Hq: q.+2 <= n.+1) ε D d :=
    C.(Frame).(restrFrame) q ε d;
|}.

(** The coherence conditions that Frame needs to satisfy to build the next level
   of Frame. These will be used in the proof script of mkFrame. *)

Definition mkLayer {n} {C: νType n} {p} {Hp: p.+1 <= n.+1}
  {Frame: FrameBlock n.+1 p mkPrefix mkFramePrev}
  {D} (d: Frame.(frame p) D): HSet :=
  hforall ε, C.(Painting).(painting) D.2 (Frame.(restrFrame) p ε d).

Definition mkLayer' {n} {C: νType n} {p} {Hp: p.+2 <= n.+1}
  {D} (d: mkFramePrev.(frame' (n := n.+1)) p D): HSet := C.(Layer) d.

Definition mkRestrLayer {n} {C: νType n} p q {Hpq: p.+2 <= q.+2}
  {Hq: q.+2 <= n.+1} {ε} {Frame: FrameBlock n.+1 p mkPrefix mkFramePrev}
  {D} {d: Frame.(frame p) D}:
  mkLayer d -> mkLayer' (Frame.(restrFrame) q.+1 ε d) :=
  fun l ω => rew [C.(PaintingPrev).(painting')] Frame.(cohFrame) p q d in
    C.(Painting).(restrPainting) p q (ε := ε) (l ω).

Definition mkCohLayer {n} {C: νType n} {p r q} {Hpr: p.+3 <= r.+3}
  {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1} {ε ω}
  {Frame: FrameBlock n.+1 p mkPrefix mkFramePrev}
  {D} {d: Frame.(frame p) D} (l: mkLayer d):
  let sl := C.(RestrLayer) p q ε (mkRestrLayer p r l) in
  let sl' := C.(RestrLayer) p r ω (mkRestrLayer p q.+1 l) in
  rew [C.(Layer')] Frame.(cohFrame) r.+1 q.+1 d in sl = sl'.
Proof.
  intros *.
  subst sl sl'; apply functional_extensionality_dep; intros 𝛉; unfold Layer'.
  rewrite <- map_subst_app with
    (P := fun 𝛉 x => C.(PaintingPrev).(painting'')
      (C.(FramePrev).(restrFrame') p p 𝛉 x)).
  unfold RestrLayer, mkRestrLayer.
  rewrite <- map_subst with (f := C.(PaintingPrev).(restrPainting') p q ε).
  rewrite <- map_subst with
    (f := C.(PaintingPrev).(restrPainting') p r ω).
  rewrite rew_map with
    (P := fun x => C.(PaintingPrev).(painting'') x)
    (f := fun x => C.(FramePrev).(restrFrame') p p 𝛉 x),
  rew_map with
    (P := fun x => C.(PaintingPrev).(painting'') x)
    (f := fun x => C.(FramePrev).(restrFrame') p q ε x),
  rew_map with
    (P := fun x => C.(PaintingPrev).(painting'') x)
    (f := fun x => C.(FramePrev).(restrFrame') p r ω x).
  rewrite <- (C.(Painting).(cohPainting) p r q).
  repeat rewrite rew_compose.
  apply rew_swap with (P := fun x => C.(PaintingPrev).(painting'') x).
  rewrite rew_app_rl. now trivial.
  now apply (C.(FramePrev).(frame'') p _).(UIP).
Qed.

(** The Frame at level n.+1 with p = O *)
#[local]
Instance mkFrame0 {n} {C: νType n}: FrameBlock n.+1 O mkPrefix mkFramePrev.
  unshelve esplit.
  * intros; now exact hunit. (* FrameSn *)
  * simpl; intros; rewrite C.(eqFrame0); now exact tt. (* restrFrameSn *)
  * simpl; intros. (* cohFramep *)
    now repeat rewrite eqRestrFrame0.
Defined.

(** The Frame at level n.+1 for p.+1 knowing the Frame at level n.+1 for p *)
#[local]
Instance mkFrameSp {n} {C: νType n} {p}
  {Frame: FrameBlock n.+1 p mkPrefix mkFramePrev}:
  FrameBlock n.+1 p.+1 mkPrefix mkFramePrev.
  unshelve esplit.
  * intros Hp D; exact {d : Frame.(frame p) D & mkLayer d}.
  * simpl; intros * ε * (d, l); invert_le Hpq. (* restrFramep *)
    now exact (rew <- [id] C.(eqFrameSp) in
      (Frame.(restrFrame) _ ε d; mkRestrLayer p q l)).
  * simpl; intros q r Hpr Hrq Hq ε ω D (d, l). (* cohframep *)
    invert_le Hpr; invert_le Hrq.

    (* A roundabout way to simplify the proof of mkCohPainting_step *)
    etransitivity.
    apply C.(eqRestrFrameSp).
    etransitivity.
    2: symmetry; apply C.(eqRestrFrameSp).

    apply f_equal with (B := C.(FramePrev).(frame') _ D.1)
      (f := fun x => rew <- (C.(eqFrameSp') (p := p)) in x).
    now exact (= Frame.(cohFrame) q.+1 r.+1 d; mkCohLayer l).
Defined.

(** Finally, we can define mkFrame at level n.+1 for all p *)
#[local]
Instance mkFrame {n} {C: νType n} p: FrameBlock n.+1 p mkPrefix mkFramePrev.
  induction p.
  * now exact mkFrame0. (* p = O *)
  * now exact mkFrameSp. (* p = S _ *)
Defined.

(** For [Painting], we take a different strategy. We first define [mkpainting],
    [mkRestrPainting], and lemmas corresponding to their computational properties *)

(** First, memoizing the previous levels of [Painting] *)
#[local]
Instance mkPaintingPrev {n} {C: νType n}:
  PaintingBlockPrev n.+1 mkPrefix mkFramePrev :=
{|
  painting' p (Hp: p.+1 <= n.+1) D := C.(Painting).(painting) D.2:
    mkFramePrev.(frame') p D -> HSet; (* Coq bug? *)
  painting'' p (Hp: p.+2 <= n.+1) D (d: mkFramePrev.(frame'') p D) :=
    C.(PaintingPrev).(painting') d;
  restrPainting' p q (Hpq: p.+2 <= q.+2) (Hq: q.+2 <= n.+1) (ε: arity) D d b :=
    C.(Painting).(restrPainting) p q (E := D.2) b;
|}.

(** Then, the component [painting] of [Painting], built by upwards induction from [p] to [n] *)

Definition mkPaintingType n {C: νType n} p {Hp: p <= n.+1} {D}
  (E: (mkFrame n.+1).(frame n.+1) D -> HSet)
  (d: (mkFrame p).(frame p) D): HSet.
Proof.
  revert d; apply le_induction with (Hp := Hp); clear p Hp.
  * now exact E. (* p = n *)
  * intros p Hp mkPaintingTypeSp d. (* p = S n *)
    now exact {l : mkLayer d & mkPaintingTypeSp (d; l)}.
Defined.

Lemma mkPaintingType_base_computes {n} {C: νType n}
  {D E} {d: (mkFrame n.+1).(frame n.+1) D}:
  mkPaintingType n n.+1 E d = E d.
Proof.
  unfold mkPaintingType; now rewrite le_induction_base_computes.
Qed.

Lemma mkPaintingType_base_computes' {n} {C: νType n}
  {D E} {d: (mkFrame n.+1).(frame n.+1) D}:
  mkPaintingType n n.+1 E d = E d :> Type.
Proof.
  unfold mkPaintingType; now rewrite le_induction_base_computes.
Qed.

Lemma mkPaintingType_step_computes {n p} {C: νType n} {Hp: p.+1 <= n.+1} {D}
  {E: (mkFrame n.+1).(frame n.+1) D -> HSet} {d}:
  mkPaintingType n p E d =
  {l : mkLayer d & mkPaintingType n p.+1 E (d; l)} :> Type.
Proof.
  unfold mkPaintingType; now rewrite le_induction_step_computes.
Qed.

(** Now, [restrPainting], and the corresponding computational properties. *)

Definition mkRestrPainting {n} {C: νType n} p q {Hpq: p.+1 <= q.+1}
  {Hq: q.+1 <= n.+1} {ε} {D} E (d: (mkFrame p).(frame p) D)
  (c: mkPaintingType n p E d):
    mkPaintingPrev.(painting') ((mkFrame p).(restrFrame) q ε d).
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
  - intros; now simpl.
  - intros; now le_contra Hp.
  - intros; now le_contra Hq.
  - intros; now le_contra Hp.
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
    eqPainting0 := ltac:(intros *; simpl; now apply mkPaintingType_base_computes');
    eqPaintingSp := ltac:(intros *; now apply mkPaintingType_step_computes);
    eqPaintingSp' := ltac:(intros *; now apply C.(eqPaintingSp));
    eqRestrPainting0 := ltac:(intros *; simpl;
      now rewrite mkRestrPainting_base_computes, rew_rew');
    eqRestrPaintingSp := ltac:(intros *; simpl;
      now rewrite mkRestrPainting_step_computes, rew_rew');
    eqRestrPainting0' := ltac:(intros *; now apply (C .(eqRestrPainting0)));
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

Arguments this {n X} _ d.
Arguments next {n X} _.

(** The final construction *)
Definition νTypes := νTypeFrom 0 tt.

Class νTypeFamily := {
 family n : νType n;
 eqPrefix {n} : (family n.+1) .(prefix) = sigT (fun D => (family n).(Frame).(frame n) D -> HSet@{m}) :> Type;
 eqFrame {n} p {Hp : p.+1 <= n.+1} {D} :
  (family n.+1) .(FramePrev) .(frame') p D = 
   (family n) .(Frame) .(frame p) (rew [id] eqPrefix in D).1 :> Type;
 eqFrame' {n} p {Hp : p.+2 <= n.+1} {D} :
   (family n.+1) .(FramePrev) .(frame'') p D = 
    (family n) .(FramePrev) .(frame') p (rew [id] eqPrefix in D).1 :> Type;
 eqRestrFrame {n} p q {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n.+1} (ε : arity) {D}
  {d : (family n.+1) .(FramePrev) .(frame') p D} :
  rew [id] (eqFrame' p) in  (family n.+1) .(FramePrev) .(restrFrame') p q ε d =
   (family n) .(Frame) .(restrFrame) q ε (rew [id] (eqFrame p) in d);
 eqPainting {n} p {Hp : p.+1 <= n.+1} {D}
  {d : (family n.+1) .(FramePrev) .(frame') p D} :
  (family n.+1) .(PaintingPrev) .(painting') d =
   (family n) .(Painting) .(painting) (rew [id] eqPrefix in D).2 (rew [id] (eqFrame p) in d) :> Type;
 eqPainting' {n} p {Hp : p.+2 <= n.+1} {D}
  {d : (family n.+1) .(FramePrev) .(frame'') p D} :
  (family n.+1) .(PaintingPrev) .(painting'') d =
   (family n) .(PaintingPrev) .(painting') (rew [id] (eqFrame' p) in d) :> Type;
 eqRestrPainting {n} p q {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n.+1} (ε : arity) {D}
  {d : (family n.+1) .(FramePrev) .(frame') p D}
  {c : (family n.+1) .(PaintingPrev) .(painting') d} :
  rew [(family n) .(PaintingPrev) .(painting')] eqRestrFrame p q ε in
  rew [id] (eqPainting' p) in (family n.+1) .(PaintingPrev) .(restrPainting') p q ε c = 
  (family n) .(Painting) .(restrPainting) p q (ε := ε) (rew [id] eqPainting p in c);
 eqFrameDistr {n} p {Hp : p.+2 <= n.+1} {D}
  {d : (family n.+1) .(FramePrev).(frame') p D}
  {l : (family n.+1) .(Layer') d} :
  rew [id] eqFrame p.+1 in rew <- [id] (family n.+1) .(eqFrameSp') in (d ; l) = 
  rew <- [id] (family n) .(eqFrameSp) in 
   (rew [id] eqFrame p in d ; 
   fun ε => rew [(family n) .(PaintingPrev) .(painting')] eqRestrFrame p p ε in rew [id] eqPainting' p in l ε);
 eqPaintingDistr {n} p {Hp : p.+2 <= n.+1} {D}
   {d : (family n.+1) .(FramePrev).(frame') p D}
   {l : (family n.+1) .(Layer') d}
   {Q : (family n.+1) .(PaintingPrev) .(painting')
        (rew <- [id] (family n.+1) .(eqFrameSp') in (d; l))} :
   rew [id] eqPainting p in rew <- [id] (family n.+1) .(eqPaintingSp') in (l ; Q) =
   rew <- [id] (family n) .(eqPaintingSp) in (
     fun ε => rew [(family n) .(PaintingPrev) .(painting')] eqRestrFrame p p ε in 
              rew [id] eqPainting' p in l ε ;
     rew [(family n) .(Painting) .(painting) ((rew [id] eqPrefix in D).2)] eqFrameDistr p in
     rew [id] eqPainting p.+1 in Q);
}.

Instance νTypeAtFamily : νTypeFamily := {|
  family := νTypeAt;
  eqPrefix := ltac:(intros; exact eq_refl);
  eqFrame := ltac:(intros; exact eq_refl);
  eqFrame' := ltac:(intros; exact eq_refl);
  eqRestrFrame := ltac:(intros; exact eq_refl);
  eqPainting := ltac:(intros; exact eq_refl);
  eqPainting' := ltac:(intros; exact eq_refl);
  eqRestrPainting := ltac:(intros; exact eq_refl);
  eqFrameDistr := ltac:(intros; exact eq_refl);
  eqPaintingDistr := ltac:(intros; exact eq_refl);
|}.

Definition find_frame {n} p q {Hpq : p <= q} {Hq : q <= n}
{C : νType n} {D : C .(prefix)}
(d : C .(Frame).(frame q) D) :
 C .(Frame).(frame p) D.
Proof.
  apply le_induction with (Hp := Hpq); clear p Hpq.
  * exact d.
  * intros p Hp d'.
    rewrite eqFrameSp in d'.
    exact d'.1.
Defined.

Definition find_frame' {n} p q {Hpq : p.+1 <= q.+1} {Hq : q.+1 <= n}
{C : νType n} {D : C .(prefix)}
(d : C .(FramePrev).(frame') q D) :
 C .(FramePrev).(frame') p D.
Proof.
  apply le_induction' with (Hp := Hpq); clear p Hpq.
  * exact d.
  * intros p Hp d'.
    rewrite eqFrameSp' in d'.
    exact d'.1.
Defined.

Definition find_painting {n} p q {Hpq : p <= q} {Hq : q <= n} {C : νType n} {D : C .(prefix)}
 {E : C .(Frame).(frame n) D -> HSet@{m}}
 {d : C .(Frame).(frame p) D}
 (l : C .(Painting) .(painting) (p := p) E d) :
 sigT (C .(Painting) .(painting) (p := q) E).
Proof.
  revert d l.
  apply le_induction with (Hp := Hpq); clear p Hpq.
  + intros d painting.
    exact (d ; painting).
  + intros p Hpq rec d painting.
    rewrite (C .(eqPaintingSp)) in painting.
    exact (rec _ painting.2).
Defined.

Definition find_painting' {n} p q {Hpq : p.+1 <= q.+1} {Hq : q.+1 <= n} {C : νType n} 
 {D : C .(prefix)}
 {d : C .(FramePrev).(frame') p D}
 (l : C .(PaintingPrev) .(painting') (p := p) d) :
 sigT (C .(PaintingPrev) .(painting') (p := q) (D := D)).
Proof.
  revert d l.
  apply le_induction' with (Hp := Hpq); clear p Hpq.
  + intros d painting.
    exact (d ; painting).
  + intros p Hpq rec d painting.
    rewrite (C .(eqPaintingSp')) in painting.
    exact (rec _ painting.2).
Defined.

Definition Face {n} p {Hp : p.+1 <= n.+1} (ε : arity)
 {Cs : νTypeFamily}
 {D : (Cs .(family) n.+1) .(prefix)}
 (d : (Cs .(family) n.+1) .(Frame).(frame n.+1) D) :
 sigT ((rew [id] (Cs .(eqPrefix)) in D).2) :=
match
  rew [fun T : Type => T] (Cs .(family) n.+1) .(eqFrameSp) in find_frame p.+1 n.+1 d
with
| (d' ; l') =>
    let p' := (find_painting p n (rew [fun T : Type => T] Cs .(eqPainting) p in l' ε)) in
    (p'.1 ; rew [id] (Cs .(family) n) .(eqPainting0) in p'.2)
end.

Lemma find_frame_compute_base {n} p {Hpq : p <= n} 
 {C : νType n} {D : C .(prefix)}
 {d : C .(Frame).(frame p) D} :
 find_frame p p d = d.
Proof.
  unfold find_frame.
  rewrite le_induction_base_computes.
  exact eq_refl.
Qed.

Lemma find_frame_compute_step {n} p q {Hpq : p.+1 <= q} {Hq : q <= n}
 {C : νType n} {D : C .(prefix)}
 {d : C .(Frame).(frame q) D} :
 find_frame p q d = 
  (rew [id] C .(eqFrameSp) in find_frame p.+1 q d).1.
Proof.
  unfold find_frame.
  rewrite le_induction_step_computes.
  exact eq_refl.
Qed.

Lemma find_painting_compute_base {n} p {Hpq : p <= n} {C : νType n} {D : C .(prefix)}
 {E : C .(Frame).(frame n) D -> HSet@{m}}
 {d : C .(Frame).(frame p) D}
 (l : C .(Painting) .(painting) (p := p) E d) :
 find_painting p p l = (d ; l).
Proof.
  unfold find_painting.
  rewrite le_induction_base_computes.
  exact eq_refl.
Qed.

Lemma find_painting_compute_step {n} p q {Hpq : p.+1 <= q} {Hq : q <= n} 
 {C : νType n} {D : C .(prefix)}
 {E : C .(Frame).(frame n) D -> HSet@{m}}
 {d : C .(Frame).(frame p) D}
 (l : C .(Painting) .(painting) (p := p) E d) :
 find_painting p q l = 
 find_painting p.+1 q (rew [id] C .(eqPaintingSp) in l).2.
Proof.
  unfold find_painting.
  rewrite le_induction_step_computes.
  exact eq_refl.
Qed.

Lemma find_frame_step {n} p q {Hpq : p.+1 <= q.+1} {Hq : q.+1 <= n} {C : νType n}
{D : C .(prefix)}
(d : C .(Frame).(frame q.+1) D) :
 find_frame p q.+1 d =
  find_frame p q (rew [id] C.(eqFrameSp) in d).1.
Proof.
  revert d.
  apply le_induction' with (Hp := Hpq); clear p Hpq.
  + intro d.
    rewrite (find_frame_compute_step q q.+1).
    now rewrite! find_frame_compute_base.
  + intros p Hpq rec d.
    rewrite (find_frame_compute_step p q.+1).
    rewrite (find_frame_compute_step p q).
    now rewrite (rec d).
Qed.

Lemma find_frame_compose {n} p q r {Hpr : p <= r} {Hrq : r <= q} {Hq : q <= n}
 {C : νType n} {D : C .(prefix)}
 {d : C .(Frame).(frame q) D} :
 find_frame p r (find_frame r q d) = find_frame p q d.
Proof.
  revert Hpr.
  apply le_induction with (Hp := Hrq); clear r Hrq.
  + now rewrite find_frame_compute_base.
  + intros r Hrq rec Hpr.
    rewrite (find_frame_compute_step r q).
    rewrite <-(find_frame_step p r (Hpq := ⇑ Hpr)).
    exact (rec _).
Qed.

Lemma find_painting_compose {n} p q r {Hpr : p <= r} {Hrq : r <= q} {Hq : q <= n}
 {C : νType n} {D : C .(prefix)}
 {E : C .(Frame).(frame n) D -> HSet@{m}}
 {d : C .(Frame).(frame p) D}
 (l : C .(Painting) .(painting) (p := p) E d) : 
 find_painting r q (find_painting p r l).2 = find_painting p q l.
Proof.
  revert d l.
  apply le_induction with (Hp := Hpr); clear p Hpr.
  + intros d l.
    now rewrite (find_painting_compute_base r l).
  + intros p Hpr rec d l.
    rewrite (find_painting_compute_step).
    rewrite (rec _ (rew [id] C .(eqPaintingSp) in l).2).
    now rewrite <-(find_painting_compute_step).
Qed.

Lemma find_frame_restr_frame {n} p q {Hpq : p.+1 <= q.+1} {Hq : q.+1 <= n.+1} {ε : arity}
 {Cs : νTypeFamily}
 {D : (Cs .(family) n.+1) .(prefix)}
 (d : (Cs .(family) n.+1) .(Frame).(frame q) D) :
 find_frame p q (rew [id] Cs .(eqFrame) q in (Cs .(family) n.+1) .(Frame) .(restrFrame) q ε d) =
 (rew [id] Cs .(eqFrame) p in (Cs .(family) n.+1) .(Frame) .(restrFrame) q ε (find_frame p q d)).
Proof.
 apply le_induction' with (Hp := Hpq) ; clear p Hpq.
 + now repeat rewrite find_frame_compute_base.
 + intros p Hpq rec.
   repeat rewrite (find_frame_compute_step p q).
   rewrite rec.
   rewrite <-(rew_opp_l id ((Cs .(family) n.+1) .(eqFrameSp)) (find_frame p.+1 q d)).
   destruct (rew [id] (Cs .(family) n.+1) .(eqFrameSp) in find_frame p.+1 q d) as [d' l'].
   invert_le Hpq.
   rewrite ((Cs .(family) n.+1) .(eqRestrFrameSp) (q := q)).
   rewrite eqFrameDistr.
   now repeat rewrite rew_opp_r.
Qed.

Lemma Test {A : Type} {B : A -> Type} {C : sigT B -> Type}
 {a a' : A} (H : a = a') (bc : sigT (fun b => (C (a ; b)))) :
 rew [B] H in bc.1 = (rew [fun a => sigT (fun b => (C (a ; b)))] H in bc).1.
Proof.
  now destruct H.
Defined.

Lemma Test' {A : Type} {B : A -> Type} {C : sigT B -> Type}
{a a' : A} (H : a = a') (bc : sigT (fun b => (C (a ; b)))) :
 rew [C] (=H ; Test H bc) in bc.2 =
 (rew [fun a => sigT (fun b => (C (a ; b)))] H in bc).2.
Proof.
  now destruct H.
Defined.

Lemma find_painting_rew {n} p q {Hpq : p <= q} {Hq : q <= n} 
{C : νType n} {D : C .(prefix)}
{E : C .(Frame).(frame n) D -> HSet@{m}}
{d d' : C .(Frame).(frame p) D}
{H : d = d'}
(l : C .(Painting) .(painting) E d) :
find_painting p q l = find_painting p q (rew [C .(Painting) .(painting) (p := p) E] H in l).
Proof.
 revert d d' H l.
 apply le_induction with (Hp := Hpq); clear p Hpq.
 + intros d d' H l.
   repeat rewrite find_painting_compute_base.
   exact (=H ; eq_refl).
 + intros p Hpq rec d d' H l.
   repeat rewrite find_painting_compute_step.
   rewrite (rew_permute_ll _ _ _ _ _ (fun _ => C .(eqPaintingSp)) H).
   simpl.
   rewrite <-(Test' (C := fun d => C .(Painting) .(painting) E (rew <- [id] C .(eqFrameSp) in d))
               H (rew [id] C .(eqPaintingSp) in l)).
   rewrite (rew_map (C .(Painting) .(painting) E) (fun ab => rew <- [id] C .(eqFrameSp) in ab)).
   apply rec.
Qed.

Definition find_frame_find_painting {n} p q r {Hpr : p <= r} {Hrq : r <= q} {Hq : q <= n}
 {C : νType n} {D : C .(prefix)}
 {E : C .(Frame).(frame n) D -> HSet@{m}}
 {d : C .(Frame).(frame p) D}
 {l : C .(Painting) .(painting) (p := p) E d} :
find_frame r q (find_painting p q l).1 = (find_painting p r l).1.
Proof.
  revert d l.
  apply le_induction with (Hp := Hpr); clear p Hpr.
  + apply le_induction with (Hp := Hrq); clear r Hrq.
    * intros d l.
      now rewrite find_frame_compute_base.
    * intros r Hqr rec d l.
      rewrite (find_frame_compute_step r q).
      rewrite (find_painting_compute_step r q).
      rewrite rec.
      repeat rewrite find_painting_compute_base.
      now rewrite rew_opp_r.
  + intros p Hpq rec d l.
    rewrite (find_painting_compute_step p q).
    rewrite (find_painting_compute_step p r).
    now rewrite rec.
Qed.

Definition destruct_painting {n} p {Hp : p.+1 <= n}
{C : νType n} 
{D : C .(prefix)}
{E : C .(Frame).(frame n) D -> HSet@{m}}
{d : C .(Frame).(frame p) D}
(l : C .(Painting) .(painting) E d) :
{l' : {l : (C .(Layer) d) & C .(Painting) .(painting) E 
  (rew <- [id] C .(eqFrameSp) in (d; l))} | rew <-[id] C .(eqPaintingSp) in l' = l}.
Proof.
  exists (rew [id] C .(eqPaintingSp) in l). now rewrite rew_opp_l.
Qed.

Definition find_painting_restr {n} p q {Hpq : p.+2 <= q.+2 } {Hq : q.+2 <= n.+2 } (ε : arity)
{Cs : νTypeFamily}
{D : (Cs .(family) n.+1) .(prefix)}
{E : (Cs .(family) n.+1) .(Frame).(frame n.+1) D -> HSet@{m}}
(d : (Cs .(family) n.+1) .(Frame).(frame p) D)
(l : (Cs .(family) n.+1) .(Painting) .(painting) E d) :
find_painting q n 
  (rew [fun T : Type => T] Cs .(eqPainting) q in
  (rew [fun T : Type => T] (Cs .(family) n.+1) .(eqFrameSp) in
  (find_painting p q.+1 l).1).2 ε) =
find_painting p n (rew [fun T : Type => T] Cs .(eqPainting) p in
 (Cs .(family) n.+1) .(Painting) .(restrPainting) p q (ε := ε) l).
Proof.
  rewrite (find_painting_compute_step p q.+1).
  revert d l.
  apply le_induction'' with (Hp := Hpq); clear p Hpq.
  + intros d l.
    rewrite find_painting_compute_base. simpl.
    destruct (destruct_painting q l) as [[l' Q] []].
    repeat rewrite rew_opp_r.
    now rewrite <-eqRestrPainting0.
  + intros p Hpq rec d l.
    invert_le Hpq.
    destruct (destruct_painting p l) as [[l' Q] []].
    rewrite ((Cs .(family) n.+1) .(eqRestrPaintingSp) p q).
    rewrite (eqPaintingDistr p).
    rewrite (find_painting_compute_step p n).
    repeat rewrite rew_opp_r. simpl.
    rewrite (rew_permute_ll _ 
     (Cs .(family) n.+1) .(PaintingPrev) .(painting') _ _ _
     (fun d => (Cs .(eqPainting) p.+1))).
    rewrite (rew_map ((Cs .(family) n) .(Painting) .(painting) (rew [id] Cs .(eqPrefix) in D).2)
     (fun d => rew [id] Cs .(eqFrame) p.+1 in d)).
    repeat rewrite <-(find_painting_rew p.+1 n).
    rewrite <-(rec).
    now rewrite (find_painting_compute_step p.+1 q.+2).
Qed.

Definition Face_coh n p q {Hpq : p.+2 <= q.+2 } {Hq : q.+2 <= n.+2 } (ε ω : arity)
 {Cs : νTypeFamily}
 {D : (Cs .(family) n.+2) .(prefix)}
 (d : (Cs .(family) n.+2) .(Frame).(frame n.+2) D) :
 (Face q ε (Face p ω d).1) = (Face p ω (Face q.+1 ε d).1).
Proof.
  unfold Face at 1 3.
  rewrite (sigT_eta 
   (rew [fun T : Type => T] (Cs .(family) n.+1) .(eqFrameSp) in 
   find_frame q.+1 n.+1 (Face p ω d).1)).
  rewrite (sigT_eta 
   (rew [fun T : Type => T] (Cs .(family) n.+1) .(eqFrameSp) in
   find_frame p.+1 n.+1 (Face q.+1 ε d).1)).
  apply (f_equal (fun l : (sigT ((Cs .(family) n) .(Painting) .(painting)
    (rew [id] Cs .(eqPrefix) in (rew [id] Cs .(eqPrefix) in D).1).2))
    => (l.1 ; rew [id] (Cs .(family) n) .(eqPainting0) in l.2))).
  unfold Face.
  rewrite (sigT_eta 
    (rew [fun T : Type => T] (Cs .(family) n.+2) .(eqFrameSp) in (find_frame p.+1 n.+2 d))).
  rewrite (sigT_eta
    (rew [fun T : Type => T] (Cs .(family) n.+2).(eqFrameSp) in find_frame q.+2 n.+2 d)).
  simpl.
  pose (find_frame_compose p.+1 n.+1 q.+1
   (d := (find_painting q.+1 n.+1
   (rew [fun T : Type => T] Cs .(eqPainting) q.+1 in
   (rew [fun T : Type => T] (Cs .(family) n.+2)  .(eqFrameSp) in
   find_frame q.+2 n.+2 d).2 ε)).1)) as e.
  rewrite <-e; clear e.
  rewrite (find_frame_find_painting q.+1 n.+1).
  rewrite find_painting_compute_base. simpl.
  rewrite <-(find_frame_compute_step q.+1 n.+2).
  rewrite (find_frame_restr_frame p.+1 q.+1).
  rewrite (find_frame_compose p.+1 n.+2 q.+1).
  rewrite (find_frame_find_painting p n.+1 q.+1).
  rewrite (find_painting_restr p q).
  set (find_frame p.+1 n.+2 d) as d2.
  rewrite <-(rew_opp_l id ((Cs .(family) n.+2) .(eqFrameSp)) d2).
  destruct (rew [id] (Cs .(family) n.+2) .(eqFrameSp) in d2) as [d3 l3].
  rewrite eqRestrFrameSp.
  rewrite eqFrameDistr.
  repeat rewrite rew_opp_r.
  rewrite <-((eqRestrPainting) p q ε). simpl.
  rewrite (rew_permute_ll _ 
      ((Cs .(family) n.+2) .(PaintingPrev) .(painting'')) _ _ _
      (fun _ => Cs .(eqPainting') p)).
  rewrite (rew_map ((Cs .(family) n.+1) .(PaintingPrev) .(painting')) 
      (fun d => rew [id] Cs .(eqFrame') p in d)).
  repeat rewrite (rew_permute_ll _ 
      ((Cs .(family) n.+1) .(PaintingPrev) .(painting')) _ _ _
      (fun _ => Cs .(eqPainting) p)).
  repeat rewrite (rew_map ((Cs .(family) n) .(Painting) .(painting) _)
      (fun d => rew [id] Cs .(eqFrame) p in d)).
  now repeat rewrite <-(find_painting_rew p n).
Qed.

(** 
idea : 
we get two function for the frames :
permuteFrameBelow n p q, p.+2 <= q.+2 <= n, 
which permutes dimensions q.+1 q.+2 in frame n p (propagate the permutation in the painting)

permuteFrame n p q, q.+2 <= p <= n
which permutes dimensions q.+1 q.+2 in frame n p (propagate the permutation in the painting
and permutes frame n q.+1 and frame n q.+2)
*)

Inductive SProd (A B : SProp) : Type :=
  pair : A -> B -> SProd A B.

Arguments pair {A B} _ _.

Section projections.
  Context {A B: SProp}.

  Definition pfst (p: SProd A B) := match p with (pair x y) => x end.
  Definition psnd (p: SProd A B) := match p with (pair x y) => y end.
End projections.
  
Definition switch {n'} p q r 
  {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n'.+2}
  {Hpr : p.+1 <= r.+1} {Hr : r.+1 <= n'.+2} :
  sigT (fun r' => SProd (p.+1 <= r'.+1) (r'.+1 <= n'.+2)) :=
  if eq_nat_dec r q then
    (q.+1 ; (pair _ _))
  else if eq_nat_dec r q.+1 then
    (q ; (pair _ _))
  else
    (r ; (pair _ _)).

Definition switch_q {n'} p q
  {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n'.+2} : 
  switch p q q = (q.+1 ; (pair _ _)).
Proof.
  unfold switch.
  destruct (eq_nat_dec q q).
  + auto.
  + contradiction.
Qed.

Definition switch_sq {n'} p q
  {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n'.+2} : 
  switch p q q.+1 = (q; (pair _ _)).
Proof.
  unfold switch.
  destruct (eq_nat_dec q.+1 q) as [H1|H1]. 2:destruct (eq_nat_dec q.+1 q.+1) as [H2|H2].
  + contradiction (n_Sn _ (eq_sym H1)).
  + auto.
  + contradiction.
Qed.

Definition switch_other {n'} p q r 
  {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n'.+2}
  {Hpr : p.+1 <= r.+1} {Hr : r.+1 <= n'.+2}
  {Hrq : r <> q} {Hrsq : r <> q.+1} :
  switch p q r = (r; (pair Hpr Hr)).
Proof.
  unfold switch.
  destruct (eq_nat_dec r q) as [H1|H1]. 2:destruct (eq_nat_dec r q.+1) as [H2|H2].
  + contradiction.
  + contradiction.
  + auto. 
Qed.

Definition switch_sp {n'} p q r {r'}
  {Hpq : p.+3 <= q.+2} {Hq : q.+2 <= n'.+2}
  {Hpr : p.+2 <= r.+1} {Hr : r.+1 <= n'.+2}
  {Hpr' : p.+2 <= r'.+1} {Hr' : r'.+1 <= n'.+2} 
  (H : switch p.+1 q r = (r' ; pair _ _)) :
  switch p q r = (r' ; pair _ _).
Proof.
  unfold switch in H|-*.
  destruct (eq_nat_dec r q). 2:destruct (eq_nat_dec r q.+1).
  + inversion H; now destruct H1.
  + inversion H; now destruct H1.
  + inversion H; now destruct H1.
Qed.

Definition switch_s {n'} p q r {r'}
  {Hpq : p.+3 <= q.+3} {Hq : q.+3 <= n'.+3}
  {Hpr : p.+2 <= r.+2} {Hr : r.+2 <= n'.+3}
  {Hpr' : p.+2 <= r'.+2} {Hr' : r'.+2 <= n'.+3} 
  (H : switch (n' := n'.+1) p.+1 q.+1 r.+1 = (r'.+1 ; pair _ _)) :
  switch (n' := n') p q r = (r' ; pair _ _).
Proof.
  unfold switch in H|-*.
  destruct (eq_nat_dec r q); destruct (eq_nat_dec r.+1 q.+1).
  + inversion H. now destruct H1.
  + destruct e. contradiction.
  + inversion e. destruct H1. contradiction.
  + destruct (eq_nat_dec r q.+1); destruct (eq_nat_dec r.+1 q.+2).
    * inversion H. now destruct H1.
    * rewrite e in n1. contradiction.
    * inversion e. rewrite H1 in n1. contradiction.
    * inversion H. now destruct H1.
Qed.

Class mkPermute T := intro_mkpermute : T -> Type@{m'}.

Class PermuteFrameBlockPrev {n'} (C: νType n'.+2) := {
  permuteFrameBelow' {p} q {Hpq : p.+3 <= q.+3} {Hq : q.+3 <= n'.+2} {D} :
  C.(FramePrev).(frame') p D -> C.(FramePrev).(frame') p D;

  permuteFrame' {p} q {Hpq : q.+3 <= p.+3} {Hq : p.+3 <= n'.+2} {D} :
  C.(FramePrev).(frame') p.+2 D -> C.(FramePrev).(frame') p.+2 D;
}.

Class PermuteFrameBelowBlock {n'} (C: νType n'.+2) p
  (PermuteFramePrev : PermuteFrameBlockPrev C) := {
  permuteFrameBelow q {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n'.+2} {D} :
    C.(Frame).(frame p) D -> C.(Frame).(frame p) D;  

  permuteFrameBelowRestrAny q r 
    {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n'.+2}
    {Hpr : p.+1 <= r.+1} {Hr : r.+1 <= n'.+2}
    {r'} {Hpr' : p.+1 <= r'.+1} {Hr' : r'.+1 <= n'.+2} 
    {D} {ε}  
    (d : C .(Frame).(frame p) D)
    (H : switch p q r = (r' ; pair Hpr' Hr')) :
    C .(Frame) .(restrFrame) r ε d = 
      C .(Frame) .(restrFrame) r' ε (permuteFrameBelow q d);
  
  permuteFrameBelowRestrQ q {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n'.+2} {D} {ε}
    (d : C .(Frame).(frame p) D) :
    C .(Frame) .(restrFrame) q ε d = 
      C .(Frame) .(restrFrame) q.+1 ε (permuteFrameBelow q d) := 
    permuteFrameBelowRestrAny q q d (switch_q _ _);

  permuteFrameBelowRestrSQ q {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n'.+2} {D} {ε}
    (d : C .(Frame).(frame p) D) :
    C .(Frame) .(restrFrame) q.+1 ε d = 
      C .(Frame) .(restrFrame) q ε (permuteFrameBelow q d) :=
    permuteFrameBelowRestrAny q q.+1 d (switch_sq _ _);

  permuteFrameBelowRestrOther q r 
    {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n'.+2}
    {Hpr : p.+1 <= r.+1} {Hr : r.+1 <= n'.+2}
    {Hrq : r <> q} {Hrsq : r <> q.+1}
    {D} {ε}  
    (d : C .(Frame).(frame p) D) :
    C .(Frame) .(restrFrame) r ε d = 
      C .(Frame) .(restrFrame) r ε (permuteFrameBelow q d) :=
    permuteFrameBelowRestrAny q r d (switch_other p q r (Hrq := Hrq) (Hrsq := Hrsq));

  eqRestrFramePermute q r 
    {Hpq : p.+3 <= q.+3} {Hq : q.+3 <= n'.+2}
    {Hpr : p.+1 <= r.+1} {Hr : r.+1 <= n'.+2} {ε} {D} 
    {d :  C .(Frame).(frame p) D} :
    C .(Frame) .(restrFrame) r ε (permuteFrameBelow q.+1 d) =
    PermuteFramePrev .(permuteFrameBelow') q (C .(Frame) .(restrFrame) r ε d);
}.

Class PermuteFrameBlock {n'} (C: νType n'.+2) p 
  {PermuteFramePrev : PermuteFrameBlockPrev C}
  (PermuteFrameBelow : forall {p}, PermuteFrameBelowBlock C p PermuteFramePrev):= {
  permuteFrame q {Hqp : q.+2 <= p.+2} {Hp : p.+2 <= n'.+2} {D} :
    C.(Frame).(frame p.+2) D -> C.(Frame).(frame p.+2) D;
}.

Class HasPermute {n'} (C: νType n'.+2)
  {PermuteFramePrev : PermuteFrameBlockPrev C}
  {PermuteFrameBelow : forall {p}, PermuteFrameBelowBlock C p PermuteFramePrev}
  {PermuteFrame : forall {p}, PermuteFrameBlock C p (@PermuteFrameBelow)}
  {D} (E : C .(Frame) .(frame n'.+2) D -> HSet) :=
  hasPermute : forall {d: C.(Frame).(frame n'.+2) D}
    q {Hqp : q.+2 <= n'.+2} ,
    E d -> E ((PermuteFrame) .(permuteFrame) q d).

Class PermutePaintingAboveBlock {n'} (C: νType n'.+2) p 
  {PermuteFramePrev : PermuteFrameBlockPrev C}
  {PermuteFrameBelow : forall {p}, PermuteFrameBelowBlock C p PermuteFramePrev}
  (PermuteFrame : forall {p}, PermuteFrameBlock C p (@PermuteFrameBelow)) := {
  permutePaintingAbove q {Hqp : q.+2 <= p.+2} {Hp : p.+2 <= n'.+2} {D E}
  {P : HasPermute C E} {d : C.(Frame).(frame p.+2) D} :
    C.(Painting).(painting) E d -> 
    C.(Painting).(painting) E (PermuteFrame .(permuteFrame) q d);
}.

Class PermutePaintingBlockPrev {n'} (C: νType n'.+2)
  (PermuteFrameBelowPrev : PermuteFrameBlockPrev C) := {
    permutePainting' p q {Hpq : p.+3 <= q.+3} {Hq : q.+3 <= n'.+2} {D}
    {d : C.(FramePrev) .(frame') p D} :
      C.(PaintingPrev).(painting') d ->
      C.(PaintingPrev).(painting') (PermuteFrameBelowPrev .(permuteFrameBelow') q d);
}.

Class PermutePaintingBlock {n'} (C: νType n'.+2) p
 {PermuteFramePrev : PermuteFrameBlockPrev C}
 (PermutePaintingPrev : PermutePaintingBlockPrev C PermuteFramePrev)
 (PermuteFrameBelow : PermuteFrameBelowBlock C p PermuteFramePrev) := {
  permutePainting q {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n'.+2} {D E}
    {d : C.(Frame).(frame p) D} :
    C.(Painting).(painting) E d ->
    C.(Painting).(painting) E (PermuteFrameBelow .(permuteFrameBelow) q d); 

  permutePaintingRestrAny q r 
    {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n'.+2} 
    {Hpr : p.+1 <= r.+1} {Hr : r.+1 <= n'.+2}
    {r'} {Hpr' : p.+1 <= r'.+1} {Hr' : r'.+1 <= n'.+2} 
    {D E} ε  
    {d : C .(Frame).(frame p) D}
    {l : C .(Painting) .(painting) E d}
    (H : switch p q r = (r' ; pair Hpr' Hr')) :
    C .(Painting) .(restrPainting) p r (ε := ε) l = 
      rew <-[C .(PaintingPrev) .(painting')] 
      PermuteFrameBelow .(permuteFrameBelowRestrAny) q r d H in
      C .(Painting) .(restrPainting) p r' (ε := ε) (permutePainting q l);

  eqRestrPaintingPermute q r
    {Hpq : p.+3 <= q.+3} {Hq : q.+3 <= n'.+2}
    {Hpr : p.+1 <= r.+1} {Hr : r.+1 <= n'.+2} {ε} {D E} 
    {d :  C .(Frame).(frame p) D}
    {l : C .(Painting) .(painting) E d} :
    C .(Painting) .(restrPainting) p r (ε := ε) (permutePainting q.+1 l) =
      rew <-[C .(PaintingPrev) .(painting')] PermuteFrameBelow .(eqRestrFramePermute) q r in
      PermutePaintingPrev .(permutePainting') p q 
        (C .(Painting) .(restrPainting) p r (ε := ε) l);
}.

Class Permute {n'} (C: νType n'.+2) := {
  PermutePrefix: mkPermute C.(prefix);
  PermuteFramePrev : PermuteFrameBlockPrev C;
  PermuteFrameBelow {p}: PermuteFrameBelowBlock C p PermuteFramePrev;
  PermuteFrame {p}: PermuteFrameBlock C p (@PermuteFrameBelow);

  PermutePaintingPrev : PermutePaintingBlockPrev C PermuteFramePrev;
  PermutePaintingAbove {p} : PermutePaintingAboveBlock C p (@PermuteFrame);
  PermutePainting {p} : PermutePaintingBlock C p PermutePaintingPrev PermuteFrameBelow;

  eqPermuteFrameBelow0 q {Hq : q.+2 <= n'.+2} {D} : 
    PermuteFrameBelow .(permuteFrameBelow) (Hpq := ⇑ ⇑ (leY_zero q)) q (D := D) 
      (rew <- [id] C .(eqFrame0) in tt) = rew <- [id] C .(eqFrame0) in tt;
  eqPermuteFrameBelowSp p q {Hpq : p.+3 <= q.+3} {Hp : q.+3 <= n'.+2} {D} 
    {d : C.(Frame).(frame p) D} {l} : 
    PermuteFrameBelow .(permuteFrameBelow) q.+1 (D := D)
      (rew <- [id] C .(eqFrameSp) in (d; l)) =
    rew <-[id] C .(eqFrameSp) in 
      (PermuteFrameBelow .(permuteFrameBelow) q.+1 d ; 
      fun ε =>  rew <- [C .(PaintingPrev) .(painting')] 
        PermuteFrameBelow .(eqRestrFramePermute) q p in
        PermutePaintingPrev .(permutePainting') p q (l ε));
}.

#[local] 
Instance mkPermutePrefix {n'} {C: νType n'.+2} {P : Permute C}: 
  mkPermute (mkνTypeSn C).(prefix) :=
  fun D => sigT (fun R : P .(PermutePrefix) D.1 => 
  HasPermute C (PermuteFrame := fun p => P .(PermuteFrame)) D.2).

#[local]
Instance mkPermuteFrameBelowPrev {n'} {C: νType n'.+2} (P : Permute C) :
  PermuteFrameBlockPrev (mkνTypeSn C).
  unshelve esplit.
  * intros p q Hpq Hq D d.
    exact ((P .(PermuteFrameBelow)) .(permuteFrameBelow) q d).
  * intros p q Hpq Hq D d.
    exact ((P .(PermuteFrame)) .(permuteFrame) q d).
Defined.

#[local]
Instance mkPermutePaintingPrev {n'} {C: νType n'.+2} (P : Permute C) :
  PermutePaintingBlockPrev (mkνTypeSn C) (mkPermuteFrameBelowPrev P).
  unshelve esplit.
  * intros p q Hpq Hq D d l.
    exact ((P .(PermutePainting)) .(permutePainting) q l). 
Defined.

#[local]
Instance mkPermuteFrameBelow0 {n'} {C: νType n'.+2} (P : Permute C) :
  PermuteFrameBelowBlock (mkνTypeSn C) O (mkPermuteFrameBelowPrev P).
  unshelve esplit.
  * intros; auto.
  * intros; auto.
  * intros. unfold mkPermuteFrameBelowPrev. simpl.
    now rewrite (P .(eqPermuteFrameBelow0)).
Defined.

#[local]
Instance mkPermuteFrameBelowSp {n'} {C: νType n'.+2} (P : Permute C) p
 (Prev : PermuteFrameBelowBlock (mkνTypeSn C) p (mkPermuteFrameBelowPrev P)) :
  PermuteFrameBelowBlock (mkνTypeSn C) p.+1 (mkPermuteFrameBelowPrev P).
  unshelve esplit.
  * intros q Hpq Hq D d.
    destruct d as [d l].
    unshelve esplit.
    + exact (Prev .(permuteFrameBelow) q d).
    + intro ε.
      invert_le Hpq.
      rewrite (Prev .(eqRestrFramePermute) q p).
      exact (P .(PermutePainting) .(permutePainting) q (l ε)).
  * intros q r Hpq Hq Hpr Hr r' Hpr' Hr' D ε d H.
    destruct d as [d l].
    invert_le Hpq. invert_le Hpr. invert_le Hpr'. simpl.
    apply (f_equal (fun d => rew <- [id] C .(eqFrameSp) in d)).
    unshelve refine (eq_existT_curried _ _).
    + exact (Prev .(permuteFrameBelowRestrAny) q.+1 r.+1 d (switch_sp _ _ _ H)).
    + apply functional_extensionality_dep. intro ω.
      rewrite <-map_subst_app.
      unfold mkRestrLayer.
      rewrite (P .(PermutePainting) .(permutePaintingRestrAny) q r ε (switch_s _ _ _ H)).
      rewrite <-(map_subst_map 
                  (Q := C .(PaintingPrev) .(painting'))
                  (fun d => C .(Frame) .(restrFrame) r' ε d)
                  (fun d c => C .(Painting) .(restrPainting) p r' c)
                  (eq_sym (Prev .(eqRestrFramePermute) q p)) _).
      rewrite (rew_map (C .(PaintingPrev) .(painting')) (C .(Frame) .(restrFrame) p ω)).
      repeat rewrite rew_compose.
      now rewrite ((C .(FramePrev) .(frame') p D.1) .(UIP) 
        (g := [d0 ⇒ C .(Frame) .(restrFrame) r' ε d0] eq_sym (Prev .(eqRestrFramePermute) q p)
            • (mkFrame p) .(cohFrame) p r' (Prev .(permuteFrameBelow) q.+1 d))).
  * intros. destruct d as [d l]. 
    invert_le Hpr. invert_le Hpq. simpl.
    rewrite (P .(eqPermuteFrameBelowSp) p q).
    apply (f_equal (fun d => rew <- [id] C .(eqFrameSp) in d)).  
    apply eq_existT_uncurried.
    unshelve esplit.
    + exact (Prev .(eqRestrFramePermute) q.+1 r.+1).
    + apply functional_extensionality_dep. intro ω.
      rewrite <-map_subst_app.
      unfold mkRestrLayer.
      rewrite <-(map_subst_map 
                  (Q := C .(PaintingPrev) .(painting'))
                  (fun d => C .(Frame) .(restrFrame) r ε d)
                  (fun d c => C .(Painting) .(restrPainting) p r c)
                  (eq_sym (Prev .(eqRestrFramePermute) q.+1 p)) _).
      rewrite ((P .(PermutePainting) (p := p)).(eqRestrPaintingPermute) q r).
      rewrite <-(map_subst_map 
                  (Q := fun d => C .(PaintingPrev) .(painting') d)
                  (fun d => P .(PermuteFramePrev) .(permuteFrameBelow') q d)
                  (fun d c => P .(PermutePaintingPrev) .(permutePainting') p q c)
                  ((mkFrame p) .(cohFrame) (Hrq := Hpr) p r d)
                  (C .(Painting) .(restrPainting) p r (l ω))).
      rewrite (rew_map (C .(PaintingPrev) .(painting')) (C .(Frame) .(restrFrame) p ω)).
      unfold eq_rect_r.
      repeat rewrite rew_compose.
      now rewrite ((C .(FramePrev) .(frame') p D.1) .(UIP)
        (g := [d0 ⇒ P .(PermuteFramePrev) .(permuteFrameBelow') q d0] (mkFrame p) .(cohFrame) p r d
            • eq_sym (P .(PermuteFrameBelow) .(eqRestrFramePermute) q p))).
Defined.

#[local] 
Instance mkPermuteFrameBelow {n'} {C: νType n'.+2} (P : Permute C) p :
  PermuteFrameBelowBlock (mkνTypeSn C) p (mkPermuteFrameBelowPrev P).
  induction p.
  + exact (mkPermuteFrameBelow0 P).
  + exact (mkPermuteFrameBelowSp P _ IHp).
Defined.

Definition destructFrame2 {n'} (C: νType n'.+2) {p} {Hp : p.+2 <= n'.+2} {D : C.(prefix)}
 (d : C .(Frame) .(frame p.+2) D) : 
 sigT (A := C .(Frame) .(frame p) D) (fun d' => 
 sigT (A := C .(Layer) d') (fun l => 
 sigT (A := C .(Layer) (rew <-[id] C .(eqFrameSp) in (d' ; l))) (fun l' =>
 d = rew <-[id] C .(eqFrameSp) in (rew <-[id] C .(eqFrameSp) in (d' ; l) ; l')
 ))).
Proof.
  remember (rew [id] C .(eqFrameSp) in d) as d'.
  destruct d' as [d' l'].
  remember (rew [id] C .(eqFrameSp) in d') as d''.
  destruct d'' as [d'' l].
  unshelve esplit. 2:unshelve esplit. 3:unshelve esplit.
  + exact d''.
  + exact l. 
  + rewrite (rew_swap_lr _ id _ _ (C .(eqFrameSp) (D := D)) _ _ Heqd'').
    exact l'.
  + rewrite <-(rew_swap_lr _ id _ _ (C .(eqFrameSp) (D := D)) _ _ Heqd').
    apply (f_equal (fun d => rew <- [id] C .(eqFrameSp) in d)).
    apply eq_existT_uncurried.
    esplit.
    exact eq_refl.
Qed.

Definition mkPermuteFrameHere {n'} p {C: νType n'.+2}
  {PermuteFrameBelowPrev : PermuteFrameBlockPrev C}
  (PermuteFrameBelow : PermuteFrameBelowBlock C p PermuteFrameBelowPrev)
  {Hq : p.+2 <= n'.+2} {D} :
  C.(Frame).(frame p.+2) D -> C.(Frame).(frame p.+2) D.
Proof.
  intro d.
  destruct (destructFrame2 C d) as [d' [l [l' eq]]]. clear d eq.
  rewrite eqFrameSp; unshelve esplit. 
  rewrite eqFrameSp; unshelve esplit.
  + exact (PermuteFrameBelow .(permuteFrameBelow) p d').
  + intro ε.
    rewrite eqPaintingSp'.
    unshelve esplit.
    * intro ω.
      rewrite <-(PermuteFrameBelow .(permuteFrameBelowRestrSQ) p).
      rewrite <-(C .(Frame) .(cohFrame)).
      exact (C .(PaintingPrev).(restrPainting') _ _ ε (l ω)).
    * refine (
        rew [C .(PaintingPrev) .(painting')] _ in 
        rew [C .(PaintingPrev) .(painting')] (C .(eqRestrFrameSp)) in
        l' ε).
      apply (f_equal (fun d => rew <- [id] C .(eqFrameSp') in d)).
      unshelve refine (eq_existT_curried _ _).
      - exact (PermuteFrameBelow .(permuteFrameBelowRestrSQ) p d').
      - apply functional_extensionality_dep. intro ω.
        rewrite <-map_subst_app. exact eq_refl.
  + intro ε.
    rewrite eqRestrFrameSp.
    refine (rew [C .(PaintingPrev) .(painting')] _ in (rew [id] (C .(eqPaintingSp')) in l ε).2).
    apply (f_equal (fun d => rew <- [id] C .(eqFrameSp') in d)).
    unshelve refine (eq_existT_curried _ _).
    * exact (PermuteFrameBelow .(permuteFrameBelowRestrQ) p d').
    * apply functional_extensionality_dep. intro ω.
      rewrite <-map_subst_app.
      rewrite <-eqRestrPainting0'.
      rewrite <-(rew_opp_l id (C .(eqPaintingSp')) _).
      rewrite (sigT_eta (rew [id] C .(eqPaintingSp') in l ε)).
      rewrite rew_opp_r.
      rewrite <-eqRestrPainting0'.
      rewrite (rew_map 
        (C .(PaintingPrev) .(painting'')) 
        (C .(FramePrev) .(restrFrame') p p ω)).
      rewrite (rew_map 
        (C .(PaintingPrev) .(painting'')) 
        (C .(FramePrev) .(restrFrame') p p ε)).
      rewrite rew_compose. rewrite rew_compose. simpl.
      apply (f_equal (fun eq =>
        rew [fun d : C .(FramePrev) .(frame'') p D => C .(PaintingPrev) .(painting'') d]
        eq in (rew [id] C .(eqPaintingSp') in l ε).1 ω)).
      exact ((C .(FramePrev) .(frame'') p D) .(UIP)).
Defined.

#[local]
Instance mkPermuteFrame0 {n'} {C: νType n'.+2}
  (PermuteFrameBelowPrev : PermuteFrameBlockPrev C)
  (PermuteFrameBelow : forall {p}, PermuteFrameBelowBlock C p PermuteFrameBelowPrev) :
  PermuteFrameBlock C O (@PermuteFrameBelow).
  unshelve esplit.
  * intros q Hpq Hp D d. exact (mkPermuteFrameHere 0 _ d).
Defined.

Inductive SLift (P : SProp): Prop :=
| lift : P -> SLift P.

Theorem foo {n p} (Hp: p <= n) : (p = n) + SLift (p.+1 <= n).
Proof.
  revert p Hp.
  induction n; intros p Hp.
  + destruct p.
    * auto.
    * le_contra Hp.
  + destruct p.
    * right. split.
      exact (⇑ (leY_zero n)).
    * case (IHn p _); intro H; destruct H.
      - auto.
      - right. split.
      exact (⇑ H).
Qed.

Instance mkPermuteFrameSp {n'} {C: νType n'.+2} (P : Permute C) p
  {PermuteFrameBelowPrev : PermuteFrameBlockPrev (mkνTypeSn C)}
  {PermuteFrameBelow : forall {p}, PermuteFrameBelowBlock (mkνTypeSn C) p PermuteFrameBelowPrev}
  (Prev : PermuteFrameBlock (mkνTypeSn C) p (@PermuteFrameBelow)) :
  PermuteFrameBlock (mkνTypeSn C) p.+1 (@PermuteFrameBelow).
  unshelve esplit.
  * intros q Hqp Hp D.
    destruct (foo Hqp) as [H | [H]].
    + inversion H. destruct H1.
      exact (mkPermuteFrameHere q (PermuteFrameBelow q)).
    + intro d. 
      destruct d as [d l].
      unshelve esplit.
      - exact (Prev .(permuteFrame) q d).
      - intro ε.
        admit.
Admitted.

(*
Instance mkPermuteFrame {n' p} {C: νType n'.+2}
  {PermuteFramePrev : PermuteFrameBlockPrev C}
  {PermuteFrameBelow : forall {p}, PermuteFrameBelowBlock C p PermuteFramePrev} :
  PermuteFrameBlock C p (@PermuteFrameBelow).
  induction p.
  + apply mkPermuteFrame0.
  + apply (mkPermuteFrameSp _ _ IHp).
Defined.
*)

Definition test {n'} {C: νType n'.+2} p {P : Permute C}
  q {Hpq : p.+2 <= q.+2} {Hq : q.+2 <= n'.+3} {D E} 
  {d : (mkνTypeSn C) .(Frame).(frame p) D} :
  (mkνTypeSn C) .(Painting).(painting) E d ->
  (mkνTypeSn C) .(Painting).(painting) E ((mkPermuteFrameBelow P p) .(permuteFrameBelow) q d).
Proof.
  revert d.
  apply le_induction'' with (Hp := Hpq); clear p Hpq.
  + intros d c.
    rewrite ((mkνTypeSn C) .(eqPaintingSp)) in c.
    destruct c as [l c].
    rewrite ((mkνTypeSn C) .(eqPaintingSp)) in c.
    destruct c as [l' c].
    rewrite ((mkνTypeSn C) .(eqPaintingSp)).
    unshelve esplit.
    * intro ε.
      rewrite ((mkνTypeSn C) .(eqPaintingSp')).
      unshelve esplit.
      - intro ω. simpl.
        rewrite <-((mkPermuteFrameBelow P q) .(permuteFrameBelowRestrSQ) q d). 
        exact (rew [C .(PaintingPrev) .(painting')] 
          (mkνTypeSn C) .(Frame) .(cohFrame) q q _ in 
          C .(Painting) .(restrPainting) q q (ε := ε) (l ω)).
      - simpl in l'|-*.
        refine (rew [fun d => C .(Painting) .(painting) D.2 (rew <- [id] C .(eqFrameSp) in d)] _ in l' ε).
        unshelve refine (eq_existT_curried _ _).
        exact ((mkPermuteFrameBelow P q) .(permuteFrameBelowRestrSQ) q d).
        apply functional_extensionality_dep.
        intro ω. now rewrite <-map_subst_app.
    * rewrite ((mkνTypeSn C) .(eqPaintingSp)).
      unshelve esplit.
      - intro ε.
        refine (rew [(mkνTypeSn C) .(PaintingPrev) .(painting')] _ in 
               (rew [id] (mkνTypeSn C) .(eqPaintingSp') in l ε).2).
        simpl.
        apply (f_equal (fun d => rew <- [id] C .(eqFrameSp) in d)).
        unshelve refine (eq_existT_curried _ _).
        exact ((mkPermuteFrameBelow P q) .(permuteFrameBelowRestrQ) q d).
        apply functional_extensionality_dep. intro ω.
        unfold mkRestrLayer.
        rewrite <-C .(eqRestrPainting0).
        admit.
      - admit.
  + intros p H rec d c.
    rewrite ((mkνTypeSn C) .(eqPaintingSp)) in c.
    destruct c as [l c].
    rewrite ((mkνTypeSn C) .(eqPaintingSp)).
    esplit.
    exact (rec _ c).
Admitted.

Instance mkPermute0: Permute (νTypeAt 2).
Proof.
  unshelve esplit.
  + unshelve esplit.
    * intros. le_contra Hq.
  + unshelve esplit.
    * intros; auto.
    * intros; invert_le Hq; invert_le Hpq; auto.
    * intros. le_contra Hq.
  + intros p. exact (mkPermuteFrame (p := p) (C := (νTypeAt 2))).
  + unshelve esplit.
    * intros; le_contra Hq.
  + admit.
  + admit.
  + intros. exact eq_refl.
  + intros. le_contra Hp.
Admitted.

(** Degeneracies *)

Class mkRefl T := intro_mkrefl : T -> Type@{m'}.
Class mk {T} (f: T -> Type@{m'}) (t: T) := intro_mk : f t.

Class DgnFrameBlockPrev {n'} (C: νType n'.+1)
  {reflPrefix: mkRefl C.(prefix)} := {
  reflFrame' p {Hp: p.+2 <= n'.+1} {D} {R: mk reflPrefix D}:
    C.(FramePrev).(frame'') p D -> C.(FramePrev).(frame') p D;
}.

Arguments reflFrame' {n' C reflPrefix} _ p {Hp D R} d.

Class DgnFrameBlock {n'} (C: νType n'.+1) {reflPrefix: mkRefl C.(prefix)}
  p (Prev: DgnFrameBlockPrev C) := {
  reflFrame {Hp: p.+1 <= n'.+1} {D} {R: mk reflPrefix D}:
    C.(FramePrev).(frame') p D -> C.(Frame).(frame p) D;
  idReflRestrFrame {ε} {Hp: p.+1 <= n'.+1} {D} {R: mk reflPrefix D}
    {d: C.(FramePrev).(frame') p D}:
    C.(Frame).(restrFrame) n' ε (reflFrame d) = d;
  cohReflRestrFrame q {ε} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n'.+1} {D}
    {R: mk reflPrefix D} {d: C.(FramePrev).(frame') p D}:
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
  hasRefl: forall (d: C.(FramePrev).(frame') n' D)
    (c: C.(PaintingPrev).(painting') d),
    let l ε :=
      rew <- [C.(PaintingPrev).(painting')] DgnFrame.(idReflRestrFrame) in c in
     E (rew <- [id] C.(eqFrameSp) in (DgnFrame.(reflFrame) d; l)).

Class DgnPaintingBlock {n'} (C: νType n'.+1) {reflPrefix: mkRefl C.(prefix)}
  {Q: DgnFrameBlockPrev C}
  (Prev: DgnPaintingBlockPrev C Q)
  (FrameBlock: forall {p}, DgnFrameBlock C p Q) := {
  reflPainting p {Hp: p.+1 <= n'.+1} {D} {R: mk reflPrefix D} {E}
    {L: HasRefl E} {d: C.(FramePrev).(frame') p D}:
    C.(PaintingPrev).(painting') d ->
    C.(Painting).(painting) E (FrameBlock.(reflFrame) d);
  idReflRestrPainting {p ε} {Hp: p.+1 <= n'.+1} {D} {R: mk reflPrefix D}
    {E} {L: HasRefl E}
    {d: C.(FramePrev).(frame') p D} {c: C.(PaintingPrev).(painting') d}:
    rew [C.(PaintingPrev).(painting')] FrameBlock.(idReflRestrFrame) in
    C.(Painting).(restrPainting) p n' (ε := ε) (E := E) (reflPainting p c) = c;
  cohReflRestrPainting {p} q {ε} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n'.+1} {D}
    {R: mk reflPrefix D} {E} {L: HasRefl E} {d: C.(FramePrev).(frame') p D}
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
    {d: C.(FramePrev).(frame') p D}
    (l: C.(Layer') d): C.(Layer) (DgnFrame.(reflFrame) d) :=
    fun ε => rew [C.(PaintingPrev).(painting')]
    DgnFrame.(cohReflRestrFrame) p in DgnPaintingPrev.(reflPainting') p (l ε);
  eqReflFrameSp {p q} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n'.+1} {D}
    {R: mk ReflPrefix D} {d: C.(FramePrev).(frame') p D} (l: C.(Layer') d):
    DgnFrame.(reflFrame) (rew <- [id] C.(eqFrameSp') in (d; l)) =
    rew <- [id] C.(eqFrameSp) in (DgnFrame.(reflFrame) d; ReflLayer l);
  eqReflPaintingSp p q {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n'.+1} {D}
    {R: mk ReflPrefix D} {E} {L: HasRefl E} {d} {l: C.(Layer') d}
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
  fun D => sigT (fun R : mk G.(ReflPrefix) D.1 =>
  HasRefl (DgnFrame := fun p => G.(DgnFrame)) D.2).

#[local]
Instance mkDgnFramePrev {n'} {C: νType n'.+1} {G: Dgn C}:
  DgnFrameBlockPrev (mkνTypeSn C) := {|
  reflFrame' p Hp (D: (mkνTypeSn C).(prefix)) R :=
    G.(DgnFrame).(reflFrame) (R := R.1);
|}.

Definition mkReflLayer {n' p} {C: νType n'.+1} {G: Dgn C}
  {Hp: p.+2 <= n'.+2} {Frame: DgnFrameBlock (mkνTypeSn C) p mkDgnFramePrev}
  {D} {R: mk mkReflPrefix D} {d: mkFramePrev.(frame') p D} (l: mkLayer' d):
  mkLayer (Frame.(reflFrame) d) :=
  fun ω => rew [C.(Painting).(painting) D.2]
    Frame.(cohReflRestrFrame) p in G.(DgnPainting).(reflPainting) (L := R.2) p
    (l ω).

Definition mkIdReflRestrLayer {n' p ε} {C: νType n'.+1} {G: Dgn C}
  {Hp: p.+2 <= n'.+2}
  {FrameBlock: DgnFrameBlock (mkνTypeSn C) p mkDgnFramePrev} {D}
  {R: mk mkReflPrefix D} {d: mkFramePrev.(frame') p D} {l: mkLayer' d}:
  rew [mkLayer'] FrameBlock.(idReflRestrFrame) (ε := ε) in
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
  now apply (C.(FramePrev).(frame') p D.1).(UIP).
Defined.

Definition mkCohReflRestrLayer {n' p} q {ε} {C: νType n'.+1} {G: Dgn C}
  {Hp: p.+3 <= q.+3} {Hq: q.+3 <= n'.+2}
  {FrameBlock: DgnFrameBlock (mkνTypeSn C) p mkDgnFramePrev} {D}
  {R: mk mkReflPrefix D} {d: mkFramePrev.(frame') p D} {l: mkLayer' (C := C) d}:
    rew [mkLayer'] FrameBlock.(cohReflRestrFrame) q.+1 in
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
  now apply (C.(FramePrev).(frame') p D.1).(UIP).
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
  {d: mkFramePrev.(frame') p D} (c: mkPaintingPrev.(painting') d):
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
  {R: mk mkReflPrefix D} {E} {L: HasRefl E} {d: mkFramePrev.(frame') n'.+1 D}
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
  {E} {L: HasRefl E} {d: mkFramePrev.(frame') p D}
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
Definition AugmentedSimplicial := sigT (νDgnTypes hunit).
Definition Cubical := sigT (νDgnTypes hbool).

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
