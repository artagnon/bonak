(** The bisimulation theory of νSets: prefix equalities and the coinductive
    levelwise equivalence [νSetFromEquiv].

    Two towers are bisimilar when their finite prefixes correspond level by
    level and their filler families correspond over that identification. The
    levelwise correspondence is converted into an *equality* of prefixes as
    soon as it is formed: univalence and functional extensionality turn the
    filler equivalences into an equality of the sigma-type prefixes
    ([prefixEq]). All restriction and coherence data of the construction is
    computed from the prefix, so transport along that equality supplies its
    compatibility.

    [prefixEqRewTotal] computes transport along a prefix equality on a
    total-space element: the frame component transports along the lower
    prefix equality, and the filler component maps through the inverse of
    the stored equivalence. This is the one place where the computation
    rules of [ua] enter. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak Require Import SigT RewLemmas HSet LeSProp Notation Univalence
  νSet.Layer νSet.
From Bonak.νSet.Lib Require Import Equiv.

From Bonak Require Import Limit.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module νSetEquiv (A: LayerSig).
Import A.

Module Export νSet := νSet.νSet A.

Definition νDataAt {m} (Xpre: (νSetAt m).(prefix)): νSetData m :=
  (νSetAt m).(data) Xpre.

Definition νTowerDeps {n} (Xpre: (νSetAt n).(prefix)): DepsRestr n 0 :=
  toDepsRestr (νDataAt Xpre).(restrFrames).

(** The full frame at a prefix, and the filler-family type over it. The
    [this] field of [νSetFrom n Xpre] has type [νFillerType Xpre], and the
    prefix one level up is [{Xpre &T νFillerType Xpre}], both definitionally.
    [νFrameDom] is the [Type]-valued version used as a transport motive. *)

Definition νFrame {n} (Xpre: (νSetAt n).(prefix)): HSet :=
  mkFrame (νTowerDeps Xpre).

Definition νFrameDom {n} (Xpre: (νSetAt n).(prefix)): Type := νFrame Xpre.

Definition νFillerType {n} (Xpre: (νSetAt n).(prefix)): Type :=
  νFrame Xpre -> HSet.

(** The construction data assembled from a prefix one level up. At a tower
    position, the pair of the prefix with the current filler assembles the
    [DepsCohs] that the face operations consume. [νFrame Xp] at level
    [n.+1] is [mkFrame (mkDepsRestr (depsCohs := prefixDepsCohs Xp))],
    definitionally. *)

Definition prefixDepsCohs {n} (Xp: (νSetAt n.+1).(prefix)): DepsCohs n 0 := {|
  _deps := νTowerDeps Xp.1;
  _extraDeps := TopRestrDep Xp.2;
  _restrPaintings := (νDataAt Xp.1).(restrPaintings) Xp.2;
  _cohs := (νDataAt Xp.1).(cohFrames) Xp.2;
|}.

(** The total space of cells at a prefix one level up — the result type of
    [νFace] at [prefixDepsCohs], as a functor of the prefix *)

Definition νTotalType {n} (Xp: (νSetAt n.+1).(prefix)): Type :=
  {d: νFrame Xp.1 &T Xp.2 d}.

(** The levelwise prefix relation, mutually with its conversion to equality

    [PrefixRelDef] at level [n.+1] pairs a relation on the lower prefixes
    with an equivalence of the filler families over the transport along the
    lower equality; [prefixEqDef] converts the relation to an equality,
    univalence and functional extensionality collapsing the filler
    equivalences ([νFillerEq]). The two are mutually recursive on the
    level, so [prefixEquivAt] builds them together. *)

Record PrefixEquivPack (n: nat) := {
  PrefixRelDef: (νSetAt n).(prefix) -> (νSetAt n).(prefix) -> Type;
  prefixEqDef: forall XA XB, PrefixRelDef XA XB -> XA = XB;
}.

Arguments PrefixRelDef {n} _ _ _.
Arguments prefixEqDef {n} _ {XA XB} _.

Definition νFillerEqvType {n} {XA XB: (νSetAt n).(prefix)} (e: XA = XB)
  (EA: νFillerType XA) (EB: νFillerType XB): Type :=
  forall d: νFrame XB, Equiv (EA (rew <- [νFrameDom] e in d)) (EB d).

(** Transporting a filler family along a prefix equality precomposes with
    the backward frame transport. The definition is transparent so that
    the equality reduces when the prefix equality is [eq_refl]. *)

Definition rewνFillerType {n} {XA XB: (νSetAt n).(prefix)} (e: XA = XB)
  (EA: νFillerType XA):
  rew [νFillerType] e in EA = fun d => EA (rew <- [νFrameDom] e in d).
Proof.
  now destruct e.
Defined.

(** The filler-family equality induced by an equivalence family: funext of
    the levelwise HSet equalities from univalence *)

Definition νFillerEq {n} {XA XB: (νSetAt n).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (eqvs: νFillerEqvType e EA EB): rew [νFillerType] e in EA = EB :=
  rewνFillerType e EA
  • functional_extensionality_dep_good _ _ (fun d => hsetEq (eqvs d)).

Fixpoint prefixEquivAt (n: nat): PrefixEquivPack n :=
  match n return PrefixEquivPack n with
  | 0 => Build_PrefixEquivPack 0
      (fun _ _ => unit)
      (fun XA XB _ => hunit_ext XA XB)
  | S n => let prev := prefixEquivAt n in
      Build_PrefixEquivPack n.+1
        (fun XA XB =>
          { r: prev.(PrefixRelDef) XA.1 XB.1 &T
            νFillerEqvType (prev.(prefixEqDef) r) XA.2 XB.2 })
        (fun XA XB r =>
          eq_existT_curried (prev.(prefixEqDef) r.1)
            (νFillerEq (prev.(prefixEqDef) r.1) r.2))
  end.

Definition PrefixRel n: (νSetAt n).(prefix) -> (νSetAt n).(prefix) -> Type :=
  (prefixEquivAt n).(PrefixRelDef).

Definition prefixEq {n} {XA XB: (νSetAt n).(prefix)}
  (r: PrefixRel n XA XB): XA = XB :=
  (prefixEquivAt n).(prefixEqDef) r.

(** The relation one level up, from filler equivalences over the current
    equality — definitionally a pair, named for the corecursion *)

Definition relStep {n} {XA XB: (νSetAt n).(prefix)} (r: PrefixRel n XA XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (eqvs: νFillerEqvType (prefixEq r) EA EB):
  PrefixRel n.+1 (XA; EA) (XB; EB) := (r; eqvs).

Definition rel0: PrefixRel 0 tt tt := tt.

(** The equality generated by [relStep] unfolds to the curried sigma
    equality of its components. *)

Definition prefixEqStep {n} {XA XB: (νSetAt n).(prefix)}
  (r: PrefixRel n XA XB) {EA: νFillerType XA} {EB: νFillerType XB}
  (eqvs: νFillerEqvType (prefixEq r) EA EB):
  prefixEq (relStep r eqvs) =
  eq_existT_curried (prefixEq r) (νFillerEq (prefixEq r) eqvs) := eq_refl.

(** Computing transport along a prefix equality

    Three steps: backward transport of a total-space pair along a sigma
    equality with a reflexive base moves only the filler component
    ([rewTotalFamily]); backward transport of the filler component along the
    funext-assembled family equality computes pointwise
    ([rewνFillerFunext]); and pointwise backward transport along [hsetEq]
    is the inverse of the equivalence ([hsetEqRewSym]).
    [prefixEqRewTotal] assembles them after destructing the lower prefix
    equality. *)

Lemma rewTotalFamily {n} {X1: (νSetAt n).(prefix)}
  {EA EB: νFillerType X1} (q: EA = EB)
  (t: νTotalType ((X1; EB): (νSetAt n.+1).(prefix))):
  rew <- [νTotalType]
    (eq_existT_curried (P := νFillerType) (eq_refl X1) q
     : ((X1; EA): (νSetAt n.+1).(prefix)) = (X1; EB)) in t =
  (t.1; rew <- [fun E: νFillerType X1 => E t.1: Type] q in t.2).
Proof.
  now destruct q.
Qed.

Lemma rewνFillerFunext {n} {X1: (νSetAt n).(prefix)}
  {EA EB: νFillerType X1} (H: forall d, EA d = EB d)
  (d0: νFrame X1) (c: EB d0):
  rew <- [fun E: νFillerType X1 => E d0: Type]
    (functional_extensionality_dep_good EA EB H) in c =
  rew <- [Dom] (H d0) in c.
Proof.
  unfold eq_rect_r.
  rewrite (rew_map (fun h: HSet => h.(Dom)) (fun E: νFillerType X1 => E d0)).
  rewrite <- eq_sym_f_equal.
  now rewrite (f_equal__functional_extensionality_dep_good H d0).
Qed.

(** The three steps assembled, for an arbitrary lower equality: path
    induction on it turns [νFillerEq] into the funext equality of the
    filler families, which the two lemmas above compute. *)

Lemma rewTotalνFillerEq {n} {XA XB: (νSetAt n).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (eqvs: νFillerEqvType e EA EB)
  (t: νTotalType ((XB; EB): (νSetAt n.+1).(prefix))):
  rew <- [νTotalType]
    (eq_existT_curried (P := νFillerType) e (νFillerEq e eqvs)
     : ((XA; EA): (νSetAt n.+1).(prefix)) = (XB; EB)) in t =
  (rew <- [νFrameDom] e in t.1; invEq (eqvs t.1) t.2).
Proof.
  destruct e.
  unfold νFillerEq; cbn [rewνFillerType].
  rewrite eq_trans_refl_l.
  rewrite (rewTotalFamily
    (functional_extensionality_dep_good _ _ (fun d => hsetEq (eqvs d))) t).
  apply (f_equal (fun c: EA t.1 =>
    ((t.1; c): νTotalType ((XA; EA): (νSetAt n.+1).(prefix))))).
  rewrite (rewνFillerFunext (fun d => hsetEq (eqvs d)) t.1 t.2).
  now apply hsetEqRewSym.
Qed.

Lemma prefixEqRewTotal {n} {XA XB: (νSetAt n.+1).(prefix)}
  (r: PrefixRel n.+1 XA XB) (t: νTotalType XB):
  rew <- [νTotalType] (prefixEq r) in t =
  (rew <- [νFrameDom] (prefixEq r.1) in t.1; invEq (r.2 t.1) t.2).
Proof.
  now exact (rewTotalνFillerEq (prefixEq r.1) r.2 t).
Qed.

(** The coinductive levelwise equivalence

    At each level: the equivalence of the current filler families over the
    prefix equality, and corecursively the equivalence of the tails over
    the extended relation. The restriction and coherence data at each level
    is computed from the prefix, so transport along the prefix equality
    supplies its compatibility. *)

CoInductive νSetFromEquiv {n} {XA XB: (νSetAt n).(prefix)}
  (r: PrefixRel n XA XB)
  (SA: νSetFrom n XA) (SB: νSetFrom n XB): Type := trCons {
  thisEquiv: νFillerEqvType (prefixEq r) (this SA) (this SB);
  nextEquiv: νSetFromEquiv (relStep r thisEquiv)
    (next SA) (next SB);
}.

End νSetEquiv.

Module νSetEquivSimplicial := νSetEquiv SimplicialLayer.
Module νSetEquivCubical := νSetEquiv CubicalLayer.
