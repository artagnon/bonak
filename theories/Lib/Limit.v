(** Telescopes and their ω-limits

    A [Telescope] is a sequence of types [stage l], each of which extends
    the one below by a single [datum]: [extend] pairs a stage with a datum
    over it, and [bond] and [head] split a stage one level up back into the
    stage below and the datum over it. The two laws [bondExtend] and
    [extendHead] state that these are mutually inverse, and
    [bondExtendHead] is the triangle identity relating them, so [stage l.+1]
    is a Σ-type over [stage l] up to the given isomorphism. The triangle is
    independent of the other two laws.

    Its ω-limit is a structure of unbounded height: a [Limit] over a stage
    [s] at level [n] is a coherent family of stages, one at every level at
    or above [n], starting at [s] and agreeing with the truncation of the
    level above. The datum at each level is recovered by [this], and [next]
    moves one level up, so a limit is consumed like the infinite nesting it
    denotes while being finite data at every level. Limits are built either
    from an already coherent family ([ofChain]) or by iterating a
    datum-producing function ([ana]).

    The three laws are fields: [stage l.+1] is a computed type, so it
    cannot be required to be a literal Σ-type over [stage l]. When an
    instance discharges them all by [eq_refl] — which
    Σ-eta for primitive records gives whenever its stages really are nested
    Σ-types — the derived operations reduce, and [this] and [next] of an
    [ana] compute to the datum-producing function.

    [limitEqIntro] is the extensionality principle: two limits over the
    same stage are equal as soon as their families of stages are, coherently
    with the two fields. It assumes functional extensionality. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak Require Import Notation SigT LeSProp RewLemmas HSet Funext.

Set Primitive Projections.
Set Printing Projections.

Record Telescope := {
  stage: nat -> Type;
  datum: forall l, stage l -> Type;
  extend: forall l (s: stage l), datum l s -> stage l.+1;
  bond: forall l, stage l.+1 -> stage l;
  head: forall l (t: stage l.+1), datum l (bond l t);
  bondExtend: forall l (s: stage l) (d: datum l s), bond l (extend l s d) = s;
  extendHead: forall l (t: stage l.+1), extend l (bond l t) (head l t) = t;
  bondExtendHead: forall l (t: stage l.+1),
    bondExtend l (bond l t) (head l t) = f_equal (bond l) (extendHead l t);
}.

Arguments stage _ _: clear implicits.
Arguments datum {_} _ _.
Arguments extend {_ _} _ _.
Arguments bond {_ _} _.
Arguments head {_ _} _.

(** A limit over [s] is a coherent family of stages: one stage at every
    level at or above [n], agreeing with [s] at [n] and with its own
    truncation one level down. *)

Record Limit (T: Telescope) n (s: T.(stage) n): Type := limit {
  approx l: n <= l -> T.(stage) l;
  approxO: approx n leR_refl = s;
  approxS l (Hl: n <= l) (HSl: n <= l.+1):
    bond (approx l.+1 HSl) = approx l Hl;
}.

Arguments approx {T n s} _ l Hl.
Arguments approxO {T n s} _.
Arguments approxS {T n s} _ l Hl HSl.

(** Destructors

    [this] reads the datum at the base level off the stage one level up,
    transporting it along the base and bonding coherences. *)

Definition this {T n s} (L: Limit T n s): T.(datum) n s :=
  rew [T.(datum) n]
    L.(approxS) n leR_refl (↑ leR_refl) • L.(approxO) in
  head (L.(approx) n.+1 (↑ leR_refl)).

(** Extending along an equality of stages moves the datum by transport. *)
Definition extendRew {T n} {s s': T.(stage) n} (e: s = s')
  (d: T.(datum) n s):
  extend s d = extend s' (rew [T.(datum) n] e in d) :=
  match e with eq_refl => eq_refl end.

(** The stage one level up is [s] extended by [this]: it is its own
    truncation extended by its own head ([extendHead]), and the two
    coherences move that statement onto [s]. *)
Definition approxEta {T n s} (L: Limit T n s):
  L.(approx) n.+1 (↑ leR_refl) = extend s (this L) :=
  eq_sym (T.(extendHead) n (L.(approx) n.+1 (↑ leR_refl)))
  • extendRew (L.(approxS) n leR_refl (↑ leR_refl) • L.(approxO))
      (head (L.(approx) n.+1 (↑ leR_refl))).

(** Truncating [approxEta] recovers the two coherences: composing it with
    [bondExtend] at the datum it produces gives back the bonding coherence
    followed by the base one. The triangle identity is what makes the two
    halves of [approxEta] cancel. *)

Lemma bondApproxEtaGen {T n} {s: T.(stage) n} (y: T.(stage) n.+1)
  (e: bond y = s):
  f_equal (fun t: T.(stage) n.+1 => bond t)
    (eq_sym (T.(extendHead) n y) • extendRew e (head y))
    • T.(bondExtend) n s (rew [T.(datum) n] e in head y)
  = e.
Proof.
  destruct e; cbn.
  rewrite <- eq_sym_f_equal.
  rewrite (T.(bondExtendHead) n y).
  now exact (eq_trans_sym_cancel_l _ eq_refl).
Qed.

Definition bondApproxEta {T n s} (L: Limit T n s):
  f_equal (fun t: T.(stage) n.+1 => bond t) (approxEta L)
    • T.(bondExtend) n s (this L)
  = L.(approxS) n leR_refl (↑ leR_refl) • L.(approxO) :=
  bondApproxEtaGen (L.(approx) n.+1 (↑ leR_refl))
    (L.(approxS) n leR_refl (↑ leR_refl) • L.(approxO)).

(** [next] reuses the family from level [n.+1] over the extended stage. *)
Definition next {T n s} (L: Limit T n s):
  Limit T n.+1 (extend s (this L)) := {|
  approx l Hl := L.(approx) l (↓ Hl);
  approxO := approxEta L;
  approxS l Hl HSl := L.(approxS) l (↓ Hl) (↓ HSl);
|}.

(** Building limits

    [ofChain] restricts a globally coherent family to the levels at or
    above [n]. If its coherence is pointwise [eq_refl] — as it is for
    families built by [mkApprox] on a telescope whose [bondExtend] is
    [eq_refl] — then [this] and [next] of the result compute. *)

Definition ofChain {T} (A: forall l, T.(stage) l)
  (HA: forall l, bond (A l.+1) = A l) n: Limit T n (A n) := {|
  approx l _ := A l;
  approxO := eq_refl;
  approxS l _ _ := HA l;
|}.

Fixpoint mkApprox {T} (z: T.(stage) 0)
  (F: forall l (s: T.(stage) l), T.(datum) l s) l: T.(stage) l :=
  match l with
  | O => z
  | l.+1 => extend (mkApprox z F l) (F l (mkApprox z F l))
  end.

Definition ana {T} (z: T.(stage) 0)
  (F: forall l (s: T.(stage) l), T.(datum) l s): Limit T 0 z :=
  ofChain (mkApprox z F) (fun l => T.(bondExtend) l _ _) 0.

(** Extensionality

    A limit is its family of stages plus two coherences, so an equality of
    limits over the same base is an equality of the families together with
    the two transported coherences. *)

Lemma limitEqIntroRaw {T n s} (L1 L2: Limit T n s)
  (e: L1.(approx) = L2.(approx))
  (eo: rew [fun a: forall l, n <= l -> T.(stage) l => a n leR_refl = s] e in
         L1.(approxO) = L2.(approxO))
  (es: forall l (Hl: n <= l) (HSl: n <= l.+1),
    rew [fun a: forall l, n <= l -> T.(stage) l =>
           bond (a l.+1 HSl) = a l Hl] e in
      L1.(approxS) l Hl HSl = L2.(approxS) l Hl HSl):
  L1 = L2.
Proof.
  destruct L1 as [a1 o1 c1], L2 as [a2 o2 c2]; cbn in e, eo, es |- *.
  revert eo es; destruct e; intros eo es; cbn in eo, es.
  assert (Hc: c1 = c2).
  { apply functional_extensionality_dep_good; intro l.
    apply spropFunext; intro Hl. apply spropFunext; intro HSl.
    exact (es l Hl HSl). }
  now destruct eo, Hc.
Qed.

(** Level [0] is where a canonical bound [leR_O] exists at every level, so
    the family of stages can be taken as a function of the level alone,
    and funext's computation rule applies to it. Above [0] the bound is not
    inhabited below the base level, and the family would have to be indexed
    by the offset instead. *)

Lemma limitEqIntro {T} {s: T.(stage) 0} (L1 L2: Limit T 0 s)
  (p: forall l, L1.(approx) l leR_O = L2.(approx) l leR_O)
  (pO: p 0 • L2.(approxO) = L1.(approxO))
  (pS: forall l,
    f_equal (fun t: T.(stage) l.+1 => bond t) (p l.+1)
      • L2.(approxS) l leR_O leR_O = L1.(approxS) l leR_O leR_O • p l):
  L1 = L2.
Proof.
  pose (q := functional_extensionality_dep_good
    (fun l => L1.(approx) l leR_O) (fun l => L2.(approx) l leR_O) p).
  pose (E := f_equal
    (fun (a: forall l, T.(stage) l) l (_: 0 <= l) => a l) q
    : L1.(approx) = L2.(approx)).
  assert (HP: forall l,
    f_equal (fun a: forall l, 0 <= l -> T.(stage) l => a l leR_O) E = p l).
  { intro l. unfold E.
    exact (eq_trans
      (f_equal_compose
        (fun (a: forall l, T.(stage) l) l (_: 0 <= l) => a l)
        (fun a: forall l, 0 <= l -> T.(stage) l => a l leR_O) q)
      (f_equal__functional_extensionality_dep_good
        (B := fun l => T.(stage) l) p l)). }
  assert (HS: forall l,
    f_equal
      (fun a: forall l, 0 <= l -> T.(stage) l => bond (a l.+1 leR_O)) E
    = f_equal (fun t: T.(stage) l.+1 => bond t) (p l.+1)).
  { intro l. unfold E.
    etransitivity.
    { exact (f_equal_compose
        (fun (a: forall l, T.(stage) l) l (_: 0 <= l) => a l)
        (fun a: forall l, 0 <= l -> T.(stage) l => bond (a l.+1 leR_O)) q). }
    etransitivity.
    { exact (eq_sym (f_equal_compose
        (fun a: forall l, T.(stage) l => a l.+1)
        (fun t: T.(stage) l.+1 => bond t) q)). }
    apply f_equal.
    exact (f_equal__functional_extensionality_dep_good
      (B := fun l => T.(stage) l) p l.+1). }
  unshelve eapply limitEqIntroRaw.
  - exact E.
  - rewrite (rew_between_const_r
      (fun a: forall l, 0 <= l -> T.(stage) l => a 0 leR_O) E).
    rewrite (HP 0).
    symmetry; now apply eq_trans_shift_l, pO.
  - intros l Hl HSl.
    rewrite (rew_between
      (fun a: forall l, 0 <= l -> T.(stage) l => bond (a l.+1 leR_O))
      (fun a: forall l, 0 <= l -> T.(stage) l => a l leR_O)).
    rewrite (HP l), (HS l).
    symmetry; now apply eq_trans_shift_l, pS.
Qed.

(** Bisimulation

    A bisimulation structure says what it means for two data over
    identified stages to correspond ([datumEqv]) and how such a
    correspondence yields an identification of them ([datumEq]). With
    proof irrelevance at the base stage, that generates a relation on
    stages at every level together with its conversion into an equality,
    the two by mutual recursion on the level. *)

Record Bisimulation (T: Telescope) := {
  stageIrr: forall x y: T.(stage) 0, x = y;
  datumEqv m (sA sB: T.(stage) m) (e: sA = sB):
    T.(datum) m sA -> T.(datum) m sB -> Type;
  datumEq m (sA sB: T.(stage) m) (e: sA = sB)
    (dA: T.(datum) m sA) (dB: T.(datum) m sB):
    datumEqv m sA sB e dA dB -> rew [T.(datum) m] e in dA = dB;
}.

Arguments stageIrr {T} _ _ _.
Arguments datumEqv {T} _ m {sA sB} e _ _.
Arguments datumEq {T} _ m {sA sB} e {dA dB} _.

(** Extending along an identification of both components *)

Definition extendCong {T m} {xA xB: T.(stage) m} (e: xA = xB)
  {dA: T.(datum) m xA} {dB: T.(datum) m xB}
  (h: rew [T.(datum) m] e in dA = dB): extend xA dA = extend xB dB :=
  match e as e0 in _ = x
    return forall d: T.(datum) m x,
      rew [T.(datum) m] e0 in dA = d -> extend xA dA = extend x d with
  | eq_refl => fun d h0 => f_equal (fun d0 => extend xA d0) h0
  end dB h.

(** The relation at a level, mutually with its conversion to equality:
    at [0] it is trivial and the conversion is proof irrelevance; one level
    up it pairs a relation on the truncations with a correspondence of the
    heads over the equality that relation yields. *)

Record RelPack (T: Telescope) (m: nat) := {
  RelDef: T.(stage) m -> T.(stage) m -> Type;
  relEqDef: forall sA sB, RelDef sA sB -> sA = sB;
}.

Arguments RelDef {T m} _ _ _.
Arguments relEqDef {T m} _ {sA sB} _.

Fixpoint relAt {T} (B: Bisimulation T) (m: nat): RelPack T m :=
  match m return RelPack T m with
  | 0 => Build_RelPack T 0 (fun _ _ => unit) (fun sA sB _ => B.(stageIrr) sA sB)
  | S m => let prev := relAt B m in
      Build_RelPack T m.+1
        (fun sA sB => { r: prev.(RelDef) (bond sA) (bond sB) &T
          B.(datumEqv) m (prev.(relEqDef) r) (head sA) (head sB) })
        (fun sA sB r =>
          rew [fun t => t = sB] T.(extendHead) m sA in
            (extendCong (prev.(relEqDef) r.1) (B.(datumEq) m _ r.2)
             • T.(extendHead) m sB))
  end.

Definition Rel {T} (B: Bisimulation T) (m: nat):
  T.(stage) m -> T.(stage) m -> Type := (relAt B m).(RelDef).

Definition relEq {T} (B: Bisimulation T) {m} {sA sB: T.(stage) m}
  (r: Rel B m sA sB): sA = sB := (relAt B m).(relEqDef) r.

(** Stepping the relation is left to the instance: [Rel] one level up
    mentions [bond] of the extended stage, which reduces to the stage below
    only when the telescope's [bondExtend] is [eq_refl]. *)
