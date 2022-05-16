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

Universe m'.
Universe m.

Parameter side: HSet.

(* PartialFrame consists of an 0-cells, and fillers which are the 1-cells,
   2-cells, and 3-cells relating the different 0-cells on the filler. *)
Class PartialFramePrev (n: nat) (csp: Type@{m'}) := { (* csp: CubeSetPrefix *)
  frame' {p} (Hp: p.+1 <= n): csp -> HSet@{m};
  frame'' {p} (Hp: p.+2 <= n): csp -> HSet@{m};
  restrFrame' {p q} {Hpq: p.+2 <= q.+2} (Hq: q.+2 <= n) (ε: side) {D: csp}:
    frame' (↓ (Hpq ↕ Hq)) D -> frame'' (Hpq ↕ Hq) D;
}.

Arguments frame' {n csp} _ {p} Hp D.
Arguments frame'' {n csp} _ {p} Hp D.
Arguments restrFrame' {n csp} _ {p q Hpq} Hq ε {D} d.

Class PartialFrame (n p: nat) (csp: Type@{m'})
  (FramePrev: PartialFramePrev n csp) := {
  frame (Hp: p <= n): csp -> HSet@{m};
  restrFrame {q} {Hpq: p.+1 <= q.+1} (Hq: q.+1 <= n) (ε: side) {D: csp}:
    frame (↓ (Hpq ↕ Hq)) D -> FramePrev.(frame') (Hpq ↕ Hq) D;
  cohFrame {q r} {Hpr: p.+2 <= r.+2} {Hrq: r.+2 <= q.+2} {Hq: q.+2 <= n}
    {ε: side} {ω: side} {D: csp} (d: frame (↓ (⇓ Hpr ↕ (↓ (Hrq ↕ Hq)))) D):
    FramePrev.(restrFrame') (Hpq := Hpr ↕ Hrq) Hq ε
      (restrFrame (Hpq := ⇓ Hpr) (↓ (Hrq ↕ Hq)) ω d) =
    (FramePrev.(restrFrame') (Hpq := Hpr) (Hrq ↕ Hq) ω
      (restrFrame (Hpq := ↓ (Hpr ↕ Hrq)) Hq ε d));
}.

Arguments frame {n p csp FramePrev} _ Hp D.
Arguments restrFrame {n p csp FramePrev} _ {q Hpq} Hq ε {D} d.
Arguments cohFrame {n p csp FramePrev} _ {q r Hpr Hrq Hq ε ω D} d.
(* We want ε and ω to be printed, but have them inferred;
   Coq doesn't support this. *)

(* We build fillers using an iterated construction: a filler at level n depends
   on cubes at level n-1 and n-2; just as we have frame' and frame'', we have
   filler' and filler''. *)
Class PartialFillerPrev (n: nat) (csp: Type@{m'})
  (FramePrev : PartialFramePrev n (@csp)) := {
  filler' {p} {Hp: p.+1 <= n} {D: csp}: FramePrev.(frame') Hp D -> HSet@{m};
  filler'' {p} {Hp: p.+2 <= n} {D: csp}: FramePrev.(frame'') Hp D -> HSet@{m};
  restrFiller' {p q} {Hpq: p.+2 <= q.+2} (Hq: q.+2 <= n) (ε: side) {D: csp}
    {d : FramePrev.(frame') (↓ (Hpq ↕ Hq)) D}:
    filler' d -> filler'' (FramePrev.(restrFrame') Hq ε d);
}.

Arguments filler' {n csp FramePrev} _ {p Hp D} d.
Arguments filler'' {n csp FramePrev} _ {p Hp D} d.
Arguments restrFiller' {n csp FramePrev} _ {p q Hpq} Hq ε {D} [d] b.

(* Filler consists of filler, restrFiller, and coherence conditions between them *)
Class PartialFiller (n: nat) (csp: Type@{m'})
  {FramePrev: PartialFramePrev n (@csp)}
  (FillerPrev: PartialFillerPrev n csp FramePrev)
  (Frame: forall {p}, PartialFrame n p (@csp) FramePrev) := {
  filler {p} {Hp: p <= n} {D: csp}:
    (Frame.(frame) (¹ n) D -> HSet@{m}) -> Frame.(frame) Hp D -> HSet@{m};
  restrFiller {p q} {Hpq: p.+1 <= q.+1}
    (Hq: q.+1 <= n) (ε: side) {D : csp} {E : Frame.(frame) (¹ n) D -> HSet@{m}}
    {d : Frame.(frame) (↓ (Hpq ↕ Hq)) D} (c : filler E d):
    FillerPrev.(filler') (Frame.(restrFrame) Hq ε d);
  cohFiller {p q r} {Hpr: p.+2 <= r.+2}
    {Hrq: r.+2 <= q.+2} {Hq: q.+2 <= n}
    (ε: side) (ω : side) {D: csp} (E: Frame.(frame) (¹ n) D -> HSet@{m})
    (d: Frame.(frame) (↓ (⇓ Hpr ↕ (↓ (Hrq ↕ Hq)))) D) (c: filler E d):
    rew [FillerPrev.(filler'')] (Frame.(cohFrame) d) in
    FillerPrev.(restrFiller') (Hpq := Hpr ↕ Hrq) Hq
    ε (restrFiller (Hpq := ⇓ Hpr) (↓ (Hrq ↕ Hq)) ω c) =
      (FillerPrev.(restrFiller') (Hpq := Hpr) (Hrq ↕ Hq)
      ω (restrFiller (Hpq := ↓ (Hpr ↕ Hrq)) Hq ε c));
}.

Arguments filler {n csp FramePrev FillerPrev Frame} _ {p Hp D} E.
Arguments restrFiller {n csp FramePrev FillerPrev Frame} _ {p q Hpq Hq ε D E} [d] c.
Arguments cohFiller {n csp FramePrev FillerPrev Frame} _ {p q r Hpr Hrq Hq ε ω D E d} c.

(* Filler consists of CubeSetPrefix, a box built out of partial boxes,
  a filler built out of partial cubes, and some axioms related to our
  construction. *)
Class NType (n : nat) := {
  csp: Type@{m'};
  FramePrev: PartialFramePrev n csp;
  Frame {p}: PartialFrame n p csp FramePrev;
  FillerPrev: PartialFillerPrev n csp FramePrev;
  Filler: PartialFiller n csp FillerPrev (@Frame);

  (* Abbreviations corresponding to coherence conditions in Box *)
  Layer' {p} {Hp: p.+1 <= n} {D: csp} (d: Frame.(frame) (↓ Hp) D) :=
    hforall ε, FillerPrev.(filler') (Frame.(restrFrame) Hp ε d);
  Layer'' {p} {Hp: p.+2 <= n} {D: csp} (d: FramePrev.(frame') (↓ Hp) D) :=
    hforall ε, FillerPrev.(filler'') (FramePrev.(restrFrame') Hp ε d);
  RestrLayer' {p q ε} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n} {D: csp}
    (d: Frame.(frame) (↓ ↓ (Hpq ↕ Hq)) D) (l: Layer' d):
      Layer'' (Frame.(restrFrame) Hq ε d) :=
  fun ω => rew [FillerPrev.(filler'')] Frame.(cohFrame) (Hrq := Hpq) d in FillerPrev.(restrFiller') Hq ε (l ω);

  (* We can't create htt: hunit, so we have to resort to this *)
  eqFrame0 {len0: 0 <= n} {D: csp}: (Frame.(frame) len0 D).(Dom) = unit;
  eqFrame0' {len1: 1 <= n} {D: csp}: (FramePrev.(frame') len1 D).(Dom) = unit;
  eqFrameSp {p} {Hp: p.+1 <= n} {D: csp}:
    Frame.(frame) Hp D = {d: Frame.(frame) (↓ Hp) D & Layer' d} :> Type;
  eqFrameSp' {p} {Hp: p.+2 <= n} {D: csp}:
    FramePrev.(frame') Hp D = {d : FramePrev.(frame') (↓ Hp) D & Layer'' d}
      :> Type;
  eqRestrFrame0 {q} {Hpq: 1 <= q.+1} {Hq: q.+1 <= n} {ε: side} {D: csp}:
    Frame.(restrFrame) (Hpq := Hpq) Hq ε (rew <- [id] eqFrame0 (D := D) in tt) =
      (rew <- [id] eqFrame0' in tt);
  eqRestrFrameSp {ε p q} {D: csp} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n}
    {d: Frame.(frame) (↓ ↓ (Hpq ↕ Hq)) D}
    {l: Layer' (Hp := ↓ (Hpq ↕ Hq)) d}:
    Frame.(restrFrame) Hq ε (rew <- [id] eqFrameSp in (d; l)) =
      rew <- [id] eqFrameSp' in (Frame.(restrFrame) Hq ε d; RestrLayer' d l);
  eqFillerSp {p} {Hp: p.+1 <= n} {D: csp} {E d}:
    Filler.(filler) (Hp := ↓ Hp) E d = {l: Layer' d &
      Filler.(filler) (D := D) E (rew <- [id] eqFrameSp in (d; l))} :> Type;
  eqFillerSp' {p} {Hp: p.+2 <= n} {D: csp} {d}:
    FillerPrev.(filler') (Hp := ↓ Hp) d = {b : Layer'' d &
      FillerPrev.(filler') (rew <- [id] eqFrameSp' (D := D) in (d; b))} :> Type;
  eqRestrFiller0 {p} {Hp: p.+1 <= n} {D: csp} {E} {d} {ε: side}
    {l: Layer' d} {Q: Filler.(filler) (D := D) E (rew <- eqFrameSp in (d; l))}:
      l ε = Filler.(restrFiller) (Hq := Hp) (rew <- [id] eqFillerSp in (l; Q));
  eqRestrFillerSp {p q} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n} {D: csp} {E} {d}
    {ε: side} {l: Layer' (Hp := ↓ (Hpq ↕ Hq)) d}
    {Q: Filler.(filler) (D := D) E (rew <- eqFrameSp in (d; l))}:
    Filler.(restrFiller) (Hpq := ↓ Hpq) (ε := ε) (rew <- [id] eqFillerSp in (l; Q)) = rew <- [id] eqFillerSp' (Hp := Hpq ↕ Hq) in
      (RestrLayer' d l; rew [FillerPrev.(filler')] eqRestrFrameSp in
        Filler.(restrFiller) Q);
}.

Arguments csp {n} _.
Arguments FramePrev {n} _.
Arguments FillerPrev {n} _.
Arguments Frame {n} _ {p}.
Arguments Filler {n} _.
Arguments Layer' {n} _ {p Hp D} d.
Arguments Layer'' {n} _ {p Hp D} d.
Arguments RestrLayer' {n} _ {p q} ε {Hpq Hq D d} l.
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

(* The csp at universe l' *)
Definition mkcsp {n} {C: NType n}: Type@{m'} :=
  sigT (fun D : C.(csp) => C.(Frame).(frame) (¹ n) D -> HSet@{m}).

(* The previous level of Box *)
Definition mkFramePrev {n} {C: NType n}: PartialFramePrev n.+1 mkcsp := {|
  frame' (p: nat) (Hp: p.+1 <= n.+1) (D: mkcsp) := C.(Frame).(frame) (⇓ Hp) D.1;
  frame'' (p: nat) (Hp: p.+2 <= n.+1) (D: mkcsp) :=
    C.(FramePrev).(frame') (⇓ Hp) D.1;
  restrFrame' (p q: nat) (Hpq: p.+2 <= q.+2) (Hq: q.+2 <= n.+1) (ε: side)
    (D: mkcsp) (d: _) :=
    C.(Frame).(restrFrame) (Hpq := ⇓ Hpq) (⇓ Hq) ε d;
|}.

(* The coherence conditions that Box needs to satisfy to build the next level
   of Frame. These will be used in the proof script of mkFrame. *)

Definition mkLayer {n p} {Hp: p.+1 <= n.+1} {C: NType n} {D: mkcsp}
  {Frame: PartialFrame n.+1 p mkcsp mkFramePrev} {d: Frame.(frame) (↓ Hp) D}: HSet :=
  hforall ε, C.(Filler).(filler) D.2 (Frame.(restrFrame) (Hpq := ¹ _) Hp ε d).

Definition mkRestrLayer {n p q} {ε: side} {Hpq: p.+2 <= q.+2} {Hq: q.+2 <= n.+1}
  {C: NType n} {D: mkcsp} {Frame: PartialFrame n.+1 p mkcsp mkFramePrev}
  (d: Frame.(frame) (↓ ↓ (Hpq ↕ Hq)) D)
  (l: mkLayer): C.(Layer') (Frame.(restrFrame) Hq ε d) :=
  fun ω => rew [C.(FillerPrev).(filler')] Frame.(cohFrame) d in
    C.(Filler).(restrFiller) (Hpq := ⇓ Hpq) (l ω).

Definition cohFrameSnHyp {n p q r} {ε ω: side} {Hpr: p.+3 <= r.+3}
  {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1} {C: NType n} {D: mkcsp}
  {frame': PartialFrame n.+1 p mkcsp mkFramePrev}
  {d: frame'.(frame) (↓ ↓ ↓ (Hpr ↕ Hrq ↕ Hq)) D}:
  C.(Frame).(restrFrame) (Hpq := ↓ ⇓ (Hpr ↕ Hrq)) (⇓ Hq) ε
    (frame'.(restrFrame) (Hpq := ↓ ⇓ Hpr) (↓ (Hrq ↕ Hq)) ω d) =
  C.(Frame).(restrFrame) (Hpq := ↓ ⇓ Hpr) (⇓ (Hrq ↕ Hq)) ω
    (frame'.(restrFrame) Hq ε d) :=
  frame'.(cohFrame) (Hpr := ↓ Hpr) (Hrq := Hrq) (Hq := Hq) d.

Definition mkCohLayer {n p q r} {ε ω: side} {Hpr: p.+3 <= r.+3}
  {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1} {C: NType n} {D: mkcsp}
  {Frame: PartialFrame n.+1 p mkcsp mkFramePrev}
  {d: Frame.(frame) (↓ ↓ ↓ (Hpr ↕ Hrq ↕ Hq)) D} (l: mkLayer):
  let sl := C.(RestrLayer') (Hpq := ⇓ (Hpr ↕ Hrq)) ε
              (mkRestrLayer (Hpq := ⇓ Hpr) d l) in
  let sl' := C.(RestrLayer') (Hpq := ⇓ Hpr) ω
               (mkRestrLayer (Hpq := ↓ (Hpr ↕ Hrq)) d l) in
  rew [C.(Layer'')] cohFrameSnHyp in sl = sl'.
Proof.
  intros *.
  subst sl sl'; apply functional_extensionality_dep; intros 𝛉; unfold Layer''.
  rewrite <- map_subst_app with
    (P := fun 𝛉 x => C.(FillerPrev).(filler'') (C.(FramePrev).(restrFrame') _ 𝛉 x))
    (f := C.(RestrLayer') _ (mkRestrLayer d l))
    (H := cohFrameSnHyp).
  unfold RestrLayer', cohFrameSnHyp, mkRestrLayer.
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
  rewrite rew_app. now reflexivity. now apply C.(FramePrev).(frame'').
Qed.

#[local]
Instance mkCubePrev {n} {C: NType n} : PartialFillerPrev n.+1 mkcsp mkFramePrev :=
{|
  filler' (p: nat) (Hp: p.+1 <= n.+1) (D: mkcsp) := C.(Filler).(filler) D.2:
    mkFramePrev.(frame') Hp D -> HSet; (* Bug? *)
  filler'' (p: nat) (Hp: p.+2 <= n.+1) (D: mkcsp)
    (d : mkFramePrev.(frame'') Hp D) :=
    C.(FillerPrev).(filler') d;
  restrFiller' (p q: nat) (Hpq: p.+2 <= q.+2) (Hq: q.+2 <= n.+1) (ε: side)
    (D: mkcsp) (d : _) (b : _) := C.(Filler).(restrFiller) (Hpq := ⇓ Hpq)
    (Hq := ⇓ Hq) (E := D.2) b;
|}.

(* The box at level n.+1 with p = O *)
#[local]
Instance mkFrame0 {n} {C: NType n}: PartialFrame n.+1 O mkcsp mkFramePrev.
  unshelve esplit.
  * intros; now exact hunit. (* boxSn *)
  * simpl; intros; rewrite C.(eqFrame0). now exact tt. (* restrFrameSn *)
  * simpl; intros. (* cohboxp *)
    now rewrite eqRestrFrame0 with (Hpq := ⇓ Hpr),
                eqRestrFrame0 with (Hpq := ⇓ (Hpr ↕ Hrq)).
Defined.

(* The box at level n.+1 with p = S _ *)
#[local]
Instance mkFrameSp {n p} {C: NType n} {Frame: PartialFrame n.+1 p mkcsp mkFramePrev}:
  PartialFrame n.+1 p.+1 mkcsp mkFramePrev.
  unshelve esplit.
  * intros Hp D; exact {d : Frame.(frame) (↓ Hp) D & mkLayer (d := d)}.
  * simpl; intros * ε * (d, l); invert_le Hpq. (* restrFramep *)
    now exact (rew <- [id] C.(eqFrameSp) in
      (Frame.(restrFrame) Hq ε d; mkRestrLayer d l)).
  * simpl; intros q r Hpr Hrq Hq ε ω D (d, l). (* cohboxp *)
    invert_le Hpr; invert_le Hrq.

    (* A roundabout way to simplify the proof of mkCohFiller_step *)
    etransitivity. apply (C.(eqRestrFrameSp) (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq)).
    etransitivity.
    2: symmetry; apply (C.(eqRestrFrameSp) (Hpq := ⇓ Hpr) (Hq := ⇓ (Hrq ↕ Hq))).

    apply f_equal with (B := C.(FramePrev).(frame') _ D.1)
      (f := fun x => rew <- (C.(eqFrameSp') (Hp := ⇓ (Hpr ↕ Hrq) ↕ ⇓ Hq)) in x).
    now exact (= (cohFrameSnHyp (Hpr := Hpr) (Hrq := Hrq)); mkCohLayer l).
    (* Bug? Coq being too smart for its own good. *)
Defined.

(* Finally, we can define mkFrame *)
#[local]
Instance mkFrame {n} {C: NType n} p: PartialFrame n.+1 p mkcsp mkFramePrev.
  induction p.
  + now exact mkFrame0. (* p = O *)
  + now exact (mkFrameSp (Frame := IHp)). (* p = S _ *)
Defined.

(* For Filler, we take a different strategy. We first define mkfiller,
   mkRestrFiller, and lemmas corresponding to their computational properties *)
(* Fist, for filler *)

Definition mkfiller {n p} {C: NType n} {Hp: p <= n.+1} {D: mkcsp}
  (E: (mkFrame n.+1).(frame) (¹ n.+1) D -> HSet)
  (d: (mkFrame p).(frame) Hp D): HSet.
  revert d; apply le_induction with (Hp := Hp); clear p Hp. (* cubeSn *)
  + now exact E. (* p = n *)
  + intros p Hp IH d; exact {l : mkLayer & IH (d; l)}. (* p = S n *)
Defined.

Lemma mkfiller_computes {n p} {C: NType n} {Hp: p.+1 <= n.+1} {D: mkcsp}
  {E: (mkFrame n.+1).(frame) (¹ n.+1) D -> HSet} {d}:
  mkfiller (Hp := ↓ Hp) E d = {l : mkLayer & mkfiller (Hp := Hp) E (d; l)} :> Type.
Proof.
  unfold mkfiller; now rewrite le_induction_step_computes.
Qed.

(* Now, restrFiller, and the corresponding computational properties. *)

Definition mkRestrFiller {n} {C: NType n} {p q} {Hpq: p.+1 <= q.+1}
  {Hq: q.+1 <= n.+1} {ε: side} {D}
  (E: (mkFrame n.+1).(frame) (¹ n.+1) D -> HSet)
  (d: (mkFrame p).(frame) (↓ (Hpq ↕ Hq)) D)
  (Filler: mkfiller (Hp := ↓ (Hpq ↕ Hq)) E d):
    mkCubePrev.(filler') ((mkFrame p).(restrFrame) Hq ε d).
Proof.
  intros *; revert d Filler; simpl. (* subcubeSn *)
  pattern p, Hpq. (* Bug? Why is this needed? *)
  apply le_induction'.
  + intros d c; rewrite mkfiller_computes in c. destruct c as (l, _).
    now exact (l ε).
  + clear p Hpq; intros p Hpq IH d c; invert_le Hpq.
    rewrite mkfiller_computes in c; destruct c as (l, c).
    change (⇓ (↓ ?Hpq ↕ ?Hq)) with (↓ ⇓ (Hpq ↕ Hq)); rewrite C.(eqFillerSp).
    apply IH in c.
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

(* Now, for the last part of the proof: proving coherence conditions
  on cohFiller *)

(* The base case is easily discharged *)
Definition mkCohFiller_base {q r n} {ε ω: side} {C: NType n} {D: mkcsp}
  {Hrq: r.+2 <= q.+2} {Hq: q.+2 <= n.+1}
  {E: (mkFrame n.+1).(frame) (¹ n.+1) D -> HSet}
  (d: (mkFrame r).(frame) (↓ ↓ (Hrq ↕ Hq)) D)
  (c: mkfiller E d):
  rew [mkCubePrev.(filler'')] (mkFrame r).(cohFrame) (Hpr := ¹ _) d in
    mkCubePrev.(restrFiller') (Hpq := Hrq) Hq ε
      (mkRestrFiller (ε := ω) (Hpq := ¹ _) (Hq := ↓ (Hrq ↕ Hq)) E d c) =
  mkCubePrev.(restrFiller') (Hpq := ¹ _) (Hrq ↕ Hq) ω
    (mkRestrFiller (ε := ε) (Hpq := ↓ Hrq) (Hq := Hq) E d c).
  change (¹ _ ↕ ?H) with H; change (⇓ ¹ _ ↕ ?H) with H.
  rewrite mkRestrFiller_base_computes, mkRestrFiller_step_computes.
  destruct (rew [id] mkfiller_computes in c) as (l, c'); clear c.
  now refine (C.(eqRestrFiller0)
    (Q := mkRestrFiller (Hpq := Hrq) E (_; _) c')).
Qed.

(* A small abbreviation *)
Definition mkCohFiller p {q r n} {ε ω: side} {C: NType n} {D: mkcsp}
  (Hpr: p.+2 <= r.+3) {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1}
  {E: (mkFrame n.+1).(frame) (¹ n.+1) D -> HSet}
  (d: (mkFrame p).(frame) (↓ ↓ (Hpr ↕ Hrq ↕ Hq)) D)
  (c: mkfiller E d) :=
  rew [mkCubePrev.(filler'')] (mkFrame p).(cohFrame) (Hrq := Hrq) d in
  C.(Filler).(restrFiller) (ε := ε) (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq)
    (mkRestrFiller (ε := ω) (Hpq := (⇓ Hpr)) (Hq := ↓ (Hrq ↕ Hq)) E d c) =
  C.(Filler).(restrFiller) (ε := ω) (Hpq := (⇓ Hpr)) (Hq := ⇓ (Hrq ↕ Hq))
    (mkRestrFiller (ε := ε) (Hpq := ↓ (Hpr ↕ Hrq)) (Hq := Hq) E d c).

(* The step case is discharged as (mkCohLayer; IHP) *)
Definition mkCohFiller_step {p q r n} {ε ω: side} {C: NType n} {D: mkcsp}
  {Hpr: p.+3 <= r.+3} {Hrq: r.+3 <= q.+3} {Hq: q.+3 <= n.+1}
  {E: (mkFrame n.+1).(frame) (¹ n.+1) D -> HSet}
  {d: (mkFrame p).(frame) (↓ ↓ (↓ Hpr ↕ Hrq ↕ Hq)) D}
  {c: mkfiller E d}
  {IHP: forall (d: (mkFrame p.+1).(frame) (↓ ↓ (Hpr ↕ Hrq ↕ Hq)) D) (c: mkfiller E d),
        mkCohFiller p.+1 Hpr (ε := ε) (ω := ω) d c}:
        mkCohFiller p (↓ Hpr) (ε := ε) (ω := ω) d c.
  unfold mkCohFiller in *; simpl projT1 in *; simpl projT2 in *.
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
  unshelve eapply (rew_existT_curried (P := C.(Layer''))
  (Q := fun x => C.(FillerPrev).(filler') (rew <- [id] C.(eqFrameSp') in x))
  (H := (mkFrame p).(cohFrame) (Hpr := ↓ Hpr) (Hrq := Hrq) (Hq := Hq) (ε := ε)
        (ω := ω) (D := D) d)
  (u := C.(RestrLayer') (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq) (D := D.1) ε
          (mkRestrLayer (Hpq := ⇓ Hpr) (Hq := ↓ (Hrq ↕ Hq)) (C := C) (D := D)
          (Frame := mkFrame p) (ε := ω) d l))
  (v := rew [C.(FillerPrev).(filler')] C.(eqRestrFrameSp) in
    C.(Filler).(restrFiller) (Hpq := ⇓ (Hpr ↕ Hrq)) (Hq := ⇓ Hq) (ε := ε)
                       (D := D.1) (E := D.2)
                       (mkRestrFiller (Hpq := ⇓ Hpr) (Hq := ↓ (Hrq ↕ Hq))
                       (D := D) (ε := ω) E (d; l) c'))).
  now exact (mkCohLayer (Hpr := Hpr) (Hrq := Hrq) (Hq := Hq) l).
  rewrite <- IHP with (d := (d; l)) (c := c').
  simpl (mkFrame p.+1). unfold mkCubePrev, filler''.
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

(* Build a PartialFiller n.+1 using what we just defined *)
#[local]
Instance mkFiller {n} {C: NType n}:
  PartialFiller n.+1 mkcsp mkCubePrev mkFrame.
  unshelve esplit; intros p.
  - intros *; now exact mkfiller.
  - intros q Hpq Hq ε d; now exact mkRestrFiller.
  - intros *. revert d c. pattern p, Hpr. apply le_induction''.
    + now exact mkCohFiller_base.
    + clear p Hpr; unfold mkCubePrev, restrFiller'; cbv beta iota;
      intros p Hpr IHP d c; invert_le Hpr; invert_le Hrq.
      now exact (mkCohFiller_step (IHP := IHP)).
Defined.

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

(* We are now ready to build a NType *)
#[local]
Instance mkNTypeSn {n} {C: NType n}: NType n.+1.
  unshelve esplit.
  - (* csp *) now exact mkcsp.
  - (* FramePrev *) now exact mkFramePrev.
  - (* Box *) now exact mkFrame.
  - (* FillerPrev *) now exact mkCubePrev.
  - (* Filler *) now exact mkFiller.
  - (* eqFrame0 *) now intros *.
  - (* eqFrame0' *) intros *; now apply C.(eqFrame0).
  - (* eqFrameSp *) now intros *.
  - (* eqFrameSp' *) intros *; now refine C.(eqFrameSp).
  - (* eqRestrFrame0 *) now intros *.
  - (* eqRestrFrameSp *) intros *; simpl; now rewrite mkfiller_computes.
  - (* eqFillerSp *) intros *; now refine C.(eqFillerSp).
  - (* eqFillerSp' *) now intros *.
  - (* eqRestrFiller0 *) intros *.
    change (fun _ (_: leR _ ?q) => _) with (¹ q); simpl.
    rewrite mkRestrFiller_base_computes.
    now rewrite eq_ind_r_refl, rew_rew'.
  - (* eqRestrFillerSp *) intros *; simpl.
    now rewrite eq_ind_r_refl, mkRestrFiller_step_computes, rew_rew'.
Defined.

Definition NTypeAt: forall n, NType n.
  induction n.
  - now exact mkNType0.
  - now exact mkNTypeSn.
Defined.

CoInductive NTypeUniverse n (X: (NTypeAt n).(csp)): Type@{m'} := cons {
  this: (NTypeAt n).(Frame).(frame) (¹ n) X -> HSet@{m};
  next: NTypeUniverse n.+1 (X; this);
}.

Definition CubeInfinity := NTypeUniverse 0 tt.
