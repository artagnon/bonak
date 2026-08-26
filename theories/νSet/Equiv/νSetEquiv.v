(** The equivalence theory of νSets: the levelwise equivalence
    [νSetsEquiv] and its conversion into an equality of towers.

    Two towers are levelwise equivalent when their finite prefixes
    correspond level by level and their filler families correspond over that
    identification. A correspondence of prefixes is turned into an equality
    as soon as it is formed ([prefixEq]), univalence and functional
    extensionality collapsing the filler equivalences. All restriction and
    coherence data of the construction is computed from the prefix, so
    transport along that equality supplies its compatibility.
    [prefixEqRewTotal] computes that transport on a total-space element: the
    frame component moves along the lower prefix equality, the filler
    component through the inverse of the stored equivalence. This is the one
    place where the computation rules of [ua] enter.

    An equality of towers then follows from [limitEqIntro], which asks for a
    family of paths between the stored prefixes commuting with the bonding
    map. The relations are indexed by [νSetPack], the unfolding whose stage
    at [m.+1] is definitionally a Σ-type over its stage at [m], whereas a
    tower stores [approx], for which that holds only up to [approxS].
    [packPath] identifies the two and [packPathS] shows the identification
    commutes with the bonding maps, so the paths transfer. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak Require Import SigT RewLemmas HSet LeSProp Notation Univalence
  νSet.Layer νSet Limit.
From Bonak.νSet.Lib Require Import Equiv.

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

    The relation at level [n.+1] pairs a relation on the lower prefixes
    with an equivalence of the filler families over the transport along the
    lower equality; converting it to an equality collapses those
    equivalences through univalence and functional extensionality
    ([νFillerEq]). Relation and conversion are mutually recursive on the
    level, which [Rel] and [relEq] build together from a [Bisimulation]. *)

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

(** The levelwise relation is the bisimulation of the νSet telescope:
    correspondence of data over a prefix path is a family of filler
    equivalences, and [νFillerEq] converts it into a path. Prefixes at
    level [0] are [unit], which supplies the base irrelevance. *)

Definition νSetBisim: Bisimulation νSetTel :=
  Build_Bisimulation νSetTel
    (fun x y => hunit_ext x y)
    (fun n XA XB e EA EB => νFillerEqvType e EA EB)
    (fun n XA XB e EA EB eqvs => νFillerEq e eqvs).

Definition PrefixRel n: (νSetAt n).(prefix) -> (νSetAt n).(prefix) -> Type :=
  Rel νSetBisim n.

Definition prefixEq {n} {XA XB: (νSetAt n).(prefix)}
  (r: PrefixRel n XA XB): XA = XB := relEq νSetBisim r.

(** The relation one level up, from filler equivalences over the current
    equality — definitionally a pair, named for the corecursion *)

Definition relStep {n} {XA XB: (νSetAt n).(prefix)} (r: PrefixRel n XA XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (eqvs: νFillerEqvType (prefixEq r) EA EB):
  PrefixRel n.+1 (XA; EA) (XB; EB) := (r; eqvs).

Definition rel0: PrefixRel 0 tt tt := tt.

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
    (extendCong (T := νSetTel) (eq_refl X1) q
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
    (extendCong (T := νSetTel) e (νFillerEq e eqvs)
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

(** Finite unfoldings of a tower

    The [m]-step unfolding of a νSet: the reached prefix, packed with the
    remaining tower so the recursion needs no arithmetic. *)

Fixpoint νSetPack (m: nat) (S: νSets):
  {Xp: (νSetAt m).(prefix) &T νSetFrom m Xp} :=
  match m with
  | 0 => (tt; S)
  | S m => (((νSetPack m S).1; this ((νSetPack m S).2));
            next ((νSetPack m S).2))
  end.

(** The levelwise equivalence

    The prefix relations form a telescope of their own: [PrefixRel] is
    indexed by the level and definitionally a Σ-type over the level below,
    whose second component is the filler equivalence at that level. So a
    levelwise equivalence of two towers is a limit of that telescope, in
    the same form as the towers it relates. The restriction and coherence
    data at each level is computed from the prefix, so transport along
    [prefixEq] supplies its compatibility. *)

Definition eqvTel (SA SB: νSets): Telescope := {|
  stage m := PrefixRel m (νSetPack m SA).1 (νSetPack m SB).1;
  datum m r := νFillerEqvType (prefixEq r)
    (this ((νSetPack m SA).2)) (this ((νSetPack m SB).2));
  extend m r E := ((r; E): PrefixRel m.+1
    (νSetPack m.+1 SA).1 (νSetPack m.+1 SB).1);
  bond m r := r.1;
  head m r := r.2;
  bondExtend m r E := eq_refl;
  extendHead m r := eq_refl;
  bondExtendHead _ _ := eq_refl;
|}.

Definition νSetsEquiv (SA SB: νSets): Type := Limit (eqvTel SA SB) 0 tt.

(** Reading the finite unfoldings off the chain

    [νSetPack] rebuilds the level-[m] prefix by iterating the
    destructors. [packPath] identifies that prefix with level [m] of the
    tower's stored chain. *)

Fixpoint packApprox (m: nat) (S: νSets) (l: nat) {struct m}:
  forall Hl: m <= l, ((νSetPack m S).2).(approx) l Hl = S.(approx) l leR_O :=
  match m return forall Hl: m <= l,
    ((νSetPack m S).2).(approx) l Hl = S.(approx) l leR_O with
  | 0 => fun _ => eq_refl
  | m.+1 => fun Hl => packApprox m S l (↓ Hl)
  end.

Definition packPath (m: nat) (S: νSets):
  (νSetPack m S).1 = S.(approx) m leR_O :=
  eq_sym ((νSetPack m S).2).(approxO)
  • packApprox m S m leR_refl.

(** Reading it off is compatible with the bonding equations:
    [νSetPack]'s own bonding equation is [eq_refl] (its prefix at [m.+1]
    is literally a pair over its prefix at [m]), the tower's is
    [approxS]. *)

Lemma packApproxS (m: nat) (S: νSets) (l: nat) (Hl: m <= l) (HSl: m <= l.+1):
  f_equal (fun Y: (νSetAt l.+1).(prefix) => Y.1) (packApprox m S l.+1 HSl)
    • S.(approxS) l leR_O leR_O
  = ((νSetPack m S).2).(approxS) l Hl HSl • packApprox m S l Hl.
Proof.
  revert l Hl HSl; induction m as [|m IH]; intros l Hl HSl.
  - cbn. now rewrite ?eq_trans_refl_l, ?eq_trans_refl_r.
  - exact (IH l (↓ Hl) (↓ HSl)).
Qed.

(** The generic truncation law at this telescope: its [bondExtend] is
    [eq_refl], so the trailing composite disappears and [bondApproxEta]
    reads as the first projection of the Σ-equality [approxEta] is built
    from. *)

Definition approxEtaProj {n} {X: (νSetAt n).(prefix)} (ν: νSetFrom n X):
  f_equal (fun Y: (νSetAt n.+1).(prefix) => Y.1) (approxEta ν)
  = ν.(approxS) n leR_refl (↑ leR_refl) • ν.(approxO) :=
  bondApproxEta ν.

Lemma packPathS (m: nat) (S: νSets):
  f_equal (fun Y: (νSetAt m.+1).(prefix) => Y.1) (packPath m.+1 S)
    • S.(approxS) m leR_O leR_O = packPath m S.
Proof.
  unfold packPath.
  change ((νSetPack m.+1 S).2).(approxO)
    with (approxEta ((νSetPack m S).2)).
  change (packApprox m.+1 S m.+1 leR_refl)
    with (packApprox m S m.+1 (↓ leR_refl)).
  rewrite eq_trans_map_distr, <- eq_sym_map_distr.
  rewrite (approxEtaProj ((νSetPack m S).2)).
  rewrite <- eq_trans_assoc.
  rewrite (packApproxS m S m leR_refl (↓ leR_refl)).
  apply eq_trans_sym_cancel_common.
Qed.

(** From coherent prefix paths to tower equality

    Conjugating the given paths by [packPath] gives paths between the
    stored prefixes, and [packPathS] turns their coherence into the square
    [limitEqIntro] asks for. The base coherence lives in the [unit] prefix
    of level 0, hence is free. *)

Lemma νSetsEqFromPaths {SA SB: νSets}
  (p: forall m, (νSetPack m SA).1 = (νSetPack m SB).1)
  (ps: forall m,
    f_equal (fun Xp: (νSetAt m.+1).(prefix) => Xp.1) (p m.+1) = p m):
  SA = SB.
Proof.
  unshelve eapply limitEqIntro.
  - exact (fun l => eq_sym (packPath l SA) • (p l • packPath l SB)).
  - now apply unit_UIP.
  - intro l; cbv beta.
    rewrite eq_trans_map_distr, eq_trans_map_distr, <- eq_sym_map_distr.
    rewrite (ps l).
    rewrite <- (packPathS l SA), <- (packPathS l SB).
    apply eq_trans_conj_comp.
Qed.

(** The chain of prefix paths generated by a levelwise equivalence

    [prefixEq] at a positive level is built by [eq_existT_curried], so its
    first projection is [prefixEq] of the relation's own first projection,
    which the bonding equation identifies with the relation one level
    down. *)

(** [extendCong] abstracts the two components of a stage as independent
    variables, which is what lets both paths be inducted on; at [prefixEq]
    they are projections of one prefix and no longer independent. *)

Lemma extendCongFst {n} {XA XB: (νSetAt n).(prefix)} (e: XA = XB)
  {EA: νFillerType XA} {EB: νFillerType XB}
  (h: rew [νFillerType] e in EA = EB):
  f_equal (fun Xp: (νSetAt n.+1).(prefix) => Xp.1)
    (extendCong (T := νSetTel) e h) = e.
Proof.
  now destruct e, h.
Qed.

Lemma prefixEqFst {m} {XA XB: (νSetAt m.+1).(prefix)}
  (r: PrefixRel m.+1 XA XB):
  f_equal (fun Xp: (νSetAt m.+1).(prefix) => Xp.1) (prefixEq r) =
  prefixEq r.1.
Proof.
  now exact (extendCongFst (prefixEq r.1) (νFillerEq (prefixEq r.1) r.2)).
Qed.

(** Convert a levelwise equivalence of towers into an equality through the
    prefix paths its stored relations generate. *)

Definition νSetsEquivEq {SA SB: νSets} (E: νSetsEquiv SA SB): SA = SB :=
  νSetsEqFromPaths
    (fun m => prefixEq (E.(approx) m leR_O))
    (fun m => prefixEqFst (E.(approx) m.+1 leR_O)
      • f_equal (@prefixEq m (νSetPack m SA).1 (νSetPack m SB).1)
          (E.(approxS) m leR_O leR_O)).

End νSetEquiv.

Module νSetEquivSimplicial := νSetEquiv SimplicialLayer.
Module νSetEquivCubical := νSetEquiv CubicalLayer.
