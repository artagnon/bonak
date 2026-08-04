Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet Notation RewLemmas.

Set Primitive Projections.
Set Printing Projections.

(** The layer former

    The νSet tower is parameterized by a shape -- simplicial or cubical.  The
    only place where the shape is felt is the *layer*: the collection of
    paintings sitting over the faces of a frame, one per element of the arity.

    This file abstracts the *layer former*. A layer is only ever required to be
    a weak product: a projection [nth], a tupling [lam], the computation rule
    [nth_lam], and extensionality [ext].

    The instantiations:

    - simplicial: [Layer B := B tt]. A layer is its single painting.
      Every structural equation holds by [eq_refl].

    - cubical: a pair [hsigT], a two-field record with primitive projections,
      so eta is definitional and [ext] is provable without an axiom. *)

Module Type LayerSig.
  Parameter arity: Type.
  Parameter Layer: forall (B: arity -> HSet), HSet.
  Parameter nth: forall {B: arity -> HSet}, Layer B -> forall ε, B ε.
  Parameter lam: forall {B: arity -> HSet}, (forall ε, B ε) -> Layer B.
  Parameter nth_lam: forall {B: arity -> HSet} (f: forall ε, B ε) ε,
    nth (lam f) ε = f ε.
  Parameter ext: forall {B: arity -> HSet} (l l': Layer B),
    (forall ε, nth l ε = nth l' ε) -> l = l'.
End LayerSig.

(** Derived combinators, shared by every layer former *)

Module LayerTheory (L: LayerSig).
Import L.

Definition lmap {B C: arity -> HSet} (f: forall ε, B ε -> C ε)
  (l: Layer B): Layer C := lam (fun ε => f ε (nth l ε)).

Lemma nth_lmap {B C: arity -> HSet} (f: forall ε, B ε -> C ε) l ε:
  nth (lmap f l) ε = f ε (nth l ε).
Proof.
  now exact (nth_lam (fun ε => f ε (nth l ε)) ε).
Defined.

(** The [map_subst] of layers: transporting a layer along a path in the frame
    commutes with taking its components. *)

Lemma nth_rew {T} {B: T -> arity -> HSet} {d1 d2} (p: d1 = d2)
  (l: Layer (B d1)) ε:
  nth (rew [fun d => Layer (B d)] p in l) ε
  = rew [fun d => B d ε] p in nth l ε.
Proof.
  now destruct p.
Defined.

Section Bridges.
Context {T X: Type} {P: X -> HSet} {rf0: arity -> T -> X}
        {d1 d2: T} {E1: d1 = d2}.

Lemma layer_rew_eq {l: Layer (fun ω => P (rf0 ω d1))}
  {l': Layer (fun ω => P (rf0 ω d2))}:
  (forall ω, rew [fun d => P (rf0 ω d)] E1 in nth l ω = nth l' ω) ->
  rew [fun d => Layer (fun ω => P (rf0 ω d))] E1 in l = l'.
Proof.
  intro H. apply ext; intro ω.
  rewrite (nth_rew (B := fun d ω => P (rf0 ω d)) E1).
  now exact (H ω).
Defined.

Lemma lam_rew_eq {f: forall ω, P (rf0 ω d1)} {g: forall ω, P (rf0 ω d2)}:
  (forall ω, rew [fun d => P (rf0 ω d)] E1 in f ω = g ω) ->
  rew [fun d => Layer (fun ω => P (rf0 ω d))] E1 in
  lam f = lam g.
Proof.
  intro H. apply layer_rew_eq; intro ω.
  rewrite 2 nth_lam. now exact (H ω).
Defined.

Lemma lam_lmap_rew_eq {B: arity -> HSet} {f: forall ω, P (rf0 ω d1)}
  {G: forall ω, B ω -> P (rf0 ω d2)} {l: Layer B}:
  (forall ω, rew [fun d => P (rf0 ω d)] E1 in f ω = G ω (nth l ω)) ->
  rew [fun d => Layer (fun ω => P (rf0 ω d))] E1 in
  lam f = lmap G l.
Proof.
  intro H. apply layer_rew_eq; intro ω.
  rewrite nth_lam, nth_lmap. now exact (H ω).
Defined.

Lemma lam_lmap_lam_rew_eq {C: arity -> HSet} {f: forall ω, P (rf0 ω d1)}
  {g: forall ω, C ω} {G: forall ω, C ω -> P (rf0 ω d2)}:
  (forall ω, rew [fun d => P (rf0 ω d)] E1 in f ω = G ω (g ω)) ->
  rew [fun d => Layer (fun ω => P (rf0 ω d))] E1 in
  lam f = lmap G (lam g).
Proof.
  intro H. apply layer_rew_eq; intro ω.
  rewrite nth_lmap, 2 nth_lam. now exact (H ω).
Defined.

Lemma layer_lmap2_rew_eq {B1: arity -> HSet} {l: Layer (fun ω => P (rf0 ω d1))}
  {G1: forall ω, P (rf0 ω d1) -> B1 ω} {G2: forall ω, B1 ω -> P (rf0 ω d2)}:
  (forall ω, rew [fun d => P (rf0 ω d)] E1 in nth l ω
             = G2 ω (G1 ω (nth l ω))) ->
  rew [fun d => Layer (fun ω => P (rf0 ω d))] E1 in
  l = lmap G2 (lmap G1 l).
Proof.
  intro H. apply layer_rew_eq; intro ω.
  rewrite 2 nth_lmap. now exact (H ω).
Defined.

Lemma lmap2_rew_eq {B B1 B2: arity -> HSet} {l: Layer B}
  {F1: forall ω, B ω -> B1 ω} {F2: forall ω, B1 ω -> P (rf0 ω d1)}
  {G1: forall ω, B ω -> B2 ω} {G2: forall ω, B2 ω -> P (rf0 ω d2)}:
  (forall ω, rew [fun d => P (rf0 ω d)] E1 in F2 ω (F1 ω (nth l ω))
             = G2 ω (G1 ω (nth l ω))) ->
  rew [fun d => Layer (fun ω => P (rf0 ω d))] E1 in
  lmap F2 (lmap F1 l) = lmap G2 (lmap G1 l).
Proof.
  intro H. apply layer_rew_eq; intro ω.
  rewrite 4 nth_lmap. now exact (H ω).
Defined.

End Bridges.

End LayerTheory.

(** The simplicial layer: no wrapper at all *)
Module SimplicialLayer <: LayerSig.
  Definition arity: Type := unit.
  Definition Layer (B: arity -> HSet): HSet := B tt.
  Definition nth {B: arity -> HSet} (l: Layer B) (ε: arity): B ε :=
    match ε with tt => l end.
  Definition lam {B: arity -> HSet} (f: forall ε, B ε): Layer B := f tt.

  Lemma nth_lam {B: arity -> HSet} (f: forall ε, B ε) ε: nth (lam f) ε = f ε.
  Proof.
    now destruct ε.
  Defined.

  Lemma ext {B: arity -> HSet} (l l': Layer B):
    (forall ε, nth l ε = nth l' ε) -> l = l'.
  Proof.
    intro H. now exact (H tt).
  Defined.
End SimplicialLayer.

(** The cubical layer: a pair [sigT], comes with definitional eta *)
Module CubicalLayer <: LayerSig.
  Definition arity: Type := bool.
  Definition Layer (B: arity -> HSet): HSet :=
    hsigT (A := B false) (fun _ => B true).

  Definition nth {B: arity -> HSet} (l: Layer B) (ε: arity): B ε :=
    match ε with false => l.1 | true => l.2 end.

  Definition lam {B: arity -> HSet} (f: forall ε, B ε): Layer B :=
    (f false; f true).

  Lemma nth_lam {B: arity -> HSet} (f: forall ε, B ε) ε: nth (lam f) ε = f ε.
  Proof.
    now destruct ε.
  Defined.

  Lemma ext {B: arity -> HSet} (l l': Layer B):
    (forall ε, nth l ε = nth l' ε) -> l = l'.
  Proof.
    intro H.
    now exact (f_equal (fun a => (a; l.2)) (H false)
             • f_equal (fun b => (l'.1; b)) (H true)).
  Defined.
End CubicalLayer.
