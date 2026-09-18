Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet νGpd.HGpd Notation RewLemmas νGpd.Pasting.

Set Primitive Projections.
Set Printing Projections.
Local Set Keyed Unification.

(** The layer former over [HGpd], for [νGpd]

    The groupoid-level counterpart of [νSet.Layer]: the same weak-product
    abstraction of the layer former. The signature is extended with the two new
    propositional facts: computation rule on [ext]-paths ([ap_nth_ext]) and the
    level-1 extensionality ([ext2]). *)

Module Type LayerGpdSig.
  Parameter arity: Type.
  Parameter Layer: forall (B: arity -> HGpd), HGpd.
  Parameter nth: forall {B: arity -> HGpd}, Layer B -> forall ε, B ε.
  Parameter lam: forall {B: arity -> HGpd}, (forall ε, B ε) -> Layer B.
  Parameter nth_lam: forall {B: arity -> HGpd} (f: forall ε, B ε) ε,
    nth (lam f) ε = f ε.
  Parameter ext: forall {B: arity -> HGpd} (l l': Layer B),
    (forall ε, nth l ε = nth l' ε) -> l = l'.
  Definition ap_nth {B: arity -> HGpd} {l l': Layer B} (p: l = l') ε:
    nth l ε = nth l' ε := f_equal (fun x => nth x ε) p.
  Parameter ap_nth_ext: forall {B: arity -> HGpd} {l l': Layer B}
    (H: forall ε, nth l ε = nth l' ε) ε, ap_nth (ext l l' H) ε = H ε.
  Parameter ext2: forall {B: arity -> HGpd} {l l': Layer B} (p q: l = l'),
    (forall ε, ap_nth p ε = ap_nth q ε) -> p = q.
End LayerGpdSig.

Module LayerGpdTheory (L: LayerGpdSig).
Import L.

Definition lmap {B C: arity -> HGpd} (f: forall ε, B ε -> C ε)
  (l: Layer B): Layer C := lam (fun ε => f ε (nth l ε)).

Lemma nth_lmap {B C: arity -> HGpd} (f: forall ε, B ε -> C ε) l ε:
  nth (lmap f l) ε = f ε (nth l ε).
Proof.
  now exact (nth_lam (fun ε => f ε (nth l ε)) ε).
Defined.

Lemma nth_rew {T} {B: T -> arity -> HGpd} {d1 d2} (p: d1 = d2)
  (l: Layer (B d1)) ε:
  nth (rew [fun d => Layer (B d)] p in l) ε
  = rew [fun d => B d ε] p in nth l ε.
Proof.
  now destruct p.
Defined.

Section Bridges.
Context {T X: Type} {P: X -> HGpd} {rf0: arity -> T -> X}
        {d1 d2: T} {E1: d1 = d2}.

(** The component homotopy is supplied for every input, allowing it to be
    evaluated at the components of any layer. *)
Definition lmap2_chain {B B1 B2: arity -> HGpd} {l: Layer B}
  {F1: forall ω, B ω -> B1 ω} {F2: forall ω, B1 ω -> P (rf0 ω d1)}
  {G1: forall ω, B ω -> B2 ω} {G2: forall ω, B2 ω -> P (rf0 ω d2)}
  (H: forall ω (a: B ω), rew [fun d => P (rf0 ω d)] E1 in F2 ω (F1 ω a)
                = G2 ω (G1 ω a)) ω:
  nth (rew [fun d => Layer (fun ω => P (rf0 ω d))] E1 in lmap F2 (lmap F1 l)) ω
  = nth (lmap G2 (lmap G1 l)) ω :=
  nth_rew (B := fun d ω => P (rf0 ω d)) E1 (lmap F2 (lmap F1 l)) ω
  • (f_equal (fun x => rew [fun d => P (rf0 ω d)] E1 in x)
       (nth_lmap F2 (lmap F1 l) ω)
     • (f_equal (fun x => rew [fun d => P (rf0 ω d)] E1 in F2 ω x)
          (nth_lmap F1 l ω)
        • (H ω (nth l ω)
           • (eq_sym (f_equal (G2 ω) (nth_lmap G1 l ω))
              • eq_sym (nth_lmap G2 (lmap G1 l) ω))))).

Definition lmap2_rew_eq {B B1 B2: arity -> HGpd} {l: Layer B}
  {F1: forall ω, B ω -> B1 ω} {F2: forall ω, B1 ω -> P (rf0 ω d1)}
  {G1: forall ω, B ω -> B2 ω} {G2: forall ω, B2 ω -> P (rf0 ω d2)}
  (H: forall ω (a: B ω), rew [fun d => P (rf0 ω d)] E1 in F2 ω (F1 ω a)
                = G2 ω (G1 ω a)):
  rew [fun d => Layer (fun ω => P (rf0 ω d))] E1 in lmap F2 (lmap F1 l)
  = lmap G2 (lmap G1 l) :=
  ext _ _ (lmap2_chain (B := B) (B1 := B1) (B2 := B2) (l := l)
    (F1 := F1) (F2 := F2) (G1 := G1) (G2 := G2) H).

End Bridges.

(** The layer coherences one level up are dependent paths: [q] lives over a
    path [p] of frames. [nth_dpath] takes such a [q] to its components, and
    every level-1 rule below is stated in terms of it. *)
Definition nth_dpath {T} {Bd: T -> arity -> HGpd} {d1 d2} {p: d1 = d2}
  {l: Layer (Bd d1)} {l': Layer (Bd d2)}
  (q: rew [fun d => Layer (Bd d)] p in l = l') ω:
  rew [fun d => Bd d ω] p in nth l ω = nth l' ω :=
  eq_sym (nth_rew p l ω) • ap_nth q ω.

(** Component evaluation is a dependent map over the frame type. *)
Lemma nth_dpath_map {T} {Bd: T -> arity -> HGpd} {d1 d2: T} {p: d1 = d2}
  {l: Layer (Bd d1)} {l': Layer (Bd d2)}
  (q: rew [fun d => Layer (Bd d)] p in l = l') ω:
  nth_dpath q ω = dpath_map (fun d l => nth l ω) q.
Proof.
  destruct p. now unfold nth_dpath, dpath_map.
Defined.

(** [nth_dpath] undoes [lmap2_rew_eq]: the components of the bridge's output
    are the components it was given, conjugated by the four [nth_lmap]
    corrections that peel the two layer maps on each side. *)
Lemma nth_dpath_lmap2_rew_eq {T X: Type} {P: X -> HGpd} {rf0: arity -> T -> X}
  {d1 d2: T} {E1: d1 = d2} {B B1 B2: arity -> HGpd} {l: Layer B}
  {F1: forall ω, B ω -> B1 ω} {F2: forall ω, B1 ω -> P (rf0 ω d1)}
  {G1: forall ω, B ω -> B2 ω} {G2: forall ω, B2 ω -> P (rf0 ω d2)}
  (H: forall ω (a: B ω), rew [fun d => P (rf0 ω d)] E1 in F2 ω (F1 ω a)
                = G2 ω (G1 ω a)) ω:
  nth_dpath (Bd := fun d ω => P (rf0 ω d))
    (lmap2_rew_eq (P := P) (rf0 := rf0) (E1 := E1) H) ω
  = dpath_change (P := fun d => GDom (P (rf0 ω d))) (nth_lmap F2 (lmap F1 l) ω)
      (dpath_change (P := fun d => GDom (P (rf0 ω d)))
        (f_equal (F2 ω) (nth_lmap F1 l ω))
        (H ω (nth l ω)) (f_equal (G2 ω) (nth_lmap G1 l ω)))
      (nth_lmap G2 (lmap G1 l) ω).
Proof.
  unfold nth_dpath, lmap2_rew_eq.
  rewrite ap_nth_ext.
  unfold lmap2_chain.
  rewrite eq_trans_sym_cancel_l.
  unfold dpath_change.
  rewrite f_equal_compose.
  now rewrite <- 2 eq_trans_assoc.
Defined.

(** [nth_dpath] is functorial for the dependent composition [⊙]. *)
Lemma nth_dpath_trans {T} {Bd: T -> arity -> HGpd} {d1 d2 d3: T}
  {p: d1 = d2} {p': d2 = d3}
  {l: Layer (Bd d1)} {l': Layer (Bd d2)} {l'': Layer (Bd d3)}
  (q: rew [fun d => Layer (Bd d)] p in l = l')
  (q': rew [fun d => Layer (Bd d)] p' in l' = l'') ω:
  nth_dpath (q ⊙[fun d => GDom (Layer (Bd d))] q') ω
  = nth_dpath q ω ⊙[fun d => GDom (Bd d ω)] nth_dpath q' ω.
Proof.
  rewrite 3 nth_dpath_map.
  now exact (dpath_map_comp (P := fun d => GDom (Layer (Bd d)))
    (Q := fun d => GDom (Bd d ω)) (fun d l => nth l ω) q q').
Defined.

(** [nth_dpath] of a mapped dependent path: [sigT_map_eq] along a layer map
    [lmap (G a)] becomes, pointwise, [sigT_map_eq] along [G a ω], with the
    two [nth_lmap] corrections at the ends. *)
Lemma nth_dpath_sigT_map_eq {T T': Type}
  {Bd: T -> arity -> HGpd} {Bd': T' -> arity -> HGpd}
  {f: T -> T'} {G: forall a ω, Bd a ω -> Bd' (f a) ω}
  {d1 d2: T} {p: d1 = d2}
  {l: Layer (Bd d1)} {l': Layer (Bd d2)}
  (q: rew [fun d => Layer (Bd d)] p in l = l') ω:
  nth_dpath (Bd := Bd')
    (sigT_map_eq (P := fun d => GDom (Layer (Bd d)))
                 (Q := fun d => GDom (Layer (Bd' d)))
                 (fun a l => lmap (G a) l) q) ω
  = dpath_change (P := fun d => GDom (Bd' d ω)) (nth_lmap (G d1) l ω)
      (sigT_map_eq (P := fun d => GDom (Bd d ω))
        (Q := fun d => GDom (Bd' d ω)) (fun a x => G a ω x) (nth_dpath q ω))
      (nth_lmap (G d2) l' ω).
Proof.
  rewrite 2 nth_dpath_map.
  now exact (dpath_map_square (P := fun d => GDom (Layer (Bd d)))
    (P' := fun d => GDom (Bd d ω))
    (Q := fun d => GDom (Layer (Bd' d))) (Q' := fun d => GDom (Bd' d ω))
    (fun d l => nth l ω) (fun d l => nth l ω)
    (fun a l => lmap (G a) l) (fun a x => G a ω x)
    (fun a l => nth_lmap (G a) l ω) q).
Defined.

(** Evaluating a two-map layer path gives its component path, with the
    computation corrections at the two endpoints. *)
Lemma sigT_map_eq_lmap2_rew_eq {T X: Type} {P: X -> HGpd} {rf0: arity -> T -> X}
  {θ: arity} {d1 d2: T} {H: d1 = d2}
  {B B1 B2: arity -> HGpd} {l: Layer B}
  {F1: forall ω, B ω -> B1 ω} {F2: forall ω, B1 ω -> P (rf0 ω d1)}
  {G1: forall ω, B ω -> B2 ω} {G2: forall ω, B2 ω -> P (rf0 ω d2)}
  (HL: forall ω (a: B ω), rew [fun d => P (rf0 ω d)] H in F2 ω (F1 ω a)
    = G2 ω (G1 ω a)):
  sigT_map_eq (P := fun d => GDom (Layer (fun ω => P (rf0 ω d))))
    (Q := fun x => GDom (P x)) (f := rf0 θ) (fun d l => nth l θ)
    (lmap2_rew_eq (P := P) (rf0 := rf0) (E1 := H) HL)
  = dpath_change (P := fun x => GDom (P x))
      (nth_lmap F2 (lmap F1 l) θ • f_equal (F2 θ) (nth_lmap F1 l θ))
      (sigT_map_eq (P := fun d => GDom (P (rf0 θ d)))
        (Q := fun x => GDom (P x)) (f := rf0 θ) (fun _ a => a) (HL θ (nth l θ)))
      (nth_lmap G2 (lmap G1 l) θ • f_equal (G2 θ) (nth_lmap G1 l θ)).
Proof.
  rewrite sigT_map_eq_dpath_map, <- (nth_dpath_map (Bd := fun d ω => P (rf0 ω d))).
  rewrite nth_dpath_lmap2_rew_eq, dpath_change_nest.
  rewrite <- (sigT_map_eq_id (P := fun x => GDom (P x)) (rf0 θ)).
  now rewrite dpath_change_map, 2 f_equal_id.
Defined.

Section Triangle.

Context {T X: Type} {P: X -> HGpd} {S: T -> HGpd}
  {rq rr: T -> X} {rf0: arity -> T -> X}
  {F: forall m, S m -> P (rq m)} {G: forall n, S n -> P (rr n)}
  {d1 d2: T} {E1: d1 = d2}
  {m1 m2 n1 n2: arity -> T}
  {e2: forall θ, m1 θ = m2 θ} {e5: forall θ, n1 θ = n2 θ}
  {pQ: forall θ, rq (m2 θ) = rf0 θ d1}
  {pR: forall θ, rr (n2 θ) = rf0 θ d2}
  {B: arity -> HGpd} {l: Layer B}
  {aL: forall θ, B θ -> S (m1 θ)} {aR: forall θ, B θ -> S (n1 θ)}.

Let F1 θ a := rew [S] e2 θ in aL θ a.
Let F2 θ b := rew [P] pQ θ in F (m2 θ) b.
Let G1 θ a := rew [S] e5 θ in aR θ a.
Let G2 θ b := rew [P] pR θ in G (n2 θ) b.

Context {HL: forall θ a,
  rew [fun d => P (rf0 θ d)] E1 in F2 θ (F1 θ a) = G2 θ (G1 θ a)}
  {θ: arity} {KA: rq (m1 θ) = rr (n1 θ)}
  {HK: rew [P] KA in F (m1 θ) (aL θ (nth l θ)) = G (n1 θ) (aR θ (nth l θ))}
  {κ: f_equal rq (e2 θ) • (pQ θ • f_equal (rf0 θ) E1) =
    KA • (f_equal rr (e5 θ) • pR θ)}.

Definition lmap2_triangle_pointwise: Type :=
  rew [fun π => rew [P] π in F (m1 θ) (aL θ (nth l θ)) =
    G2 θ (G1 θ (nth l θ))] κ in
  (sigT_map_eq (Q := fun x => GDom (P x)) F (p := e2 θ) eq_refl
   ⊙[fun x => GDom (P x)] (eq_refl ⊙[fun x => GDom (P x)]
     sigT_map_eq (P := fun d => GDom (P (rf0 θ d)))
       (Q := fun x => GDom (P x)) (f := rf0 θ) (fun _ a => a) (HL θ (nth l θ)))) =
  HK ⊙[fun x => GDom (P x)]
    (sigT_map_eq (Q := fun x => GDom (P x)) G (p := e5 θ) eq_refl
     ⊙[fun x => GDom (P x)] eq_refl).

(** Evaluating a layer triangle cancels the computation corrections at
    its shared vertices, leaving the pointwise triangle. *)
Lemma lmap2_triangle_rew_eq:
  lmap2_triangle_pointwise ->
  rew [fun π => rew [P] π in F (m1 θ) (aL θ (nth l θ)) =
    nth (lmap G2 (lmap G1 l)) θ] κ in
  (sigT_map_eq (Q := fun x => GDom (P x)) F (eq_sym (nth_lmap F1 l θ))
   ⊙[fun x => GDom (P x)]
     (eq_sym (nth_lmap F2 (lmap F1 l) θ)
      ⊙[fun x => GDom (P x)]
        sigT_map_eq (P := fun d => GDom (Layer (fun ω => P (rf0 ω d))))
          (Q := fun x => GDom (P x)) (f := rf0 θ) (fun d u => nth u θ)
          (lmap2_rew_eq (P := P) (rf0 := rf0) (E1 := E1) HL))) =
  HK ⊙[fun x => GDom (P x)]
    (sigT_map_eq (Q := fun x => GDom (P x)) G (eq_sym (nth_lmap G1 l θ))
     ⊙[fun x => GDom (P x)] eq_sym (nth_lmap G2 (lmap G1 l) θ)).
Proof.
  intro Hpointwise.
  rewrite (sigT_map_eq_lmap2_rew_eq (P := P) (rf0 := rf0) (θ := θ) (l := l)
    (F1 := F1) (F2 := F2) (G1 := G1) (G2 := G2) HL).
  rewrite <- (dpath_change_refl (P := fun x => GDom (S x)) (e2 θ)
    (aL θ (nth l θ)) (nth_lmap F1 l θ)).
  rewrite <- (dpath_change_refl (P := fun x => GDom (S x)) (e5 θ)
    (aR θ (nth l θ)) (nth_lmap G1 l θ)).
  rewrite <- (dpath_change_transport (P := fun x => GDom (P x)) (pQ θ)
    (f_equal (F (m2 θ)) (nth_lmap F1 l θ)) (nth_lmap F2 (lmap F1 l) θ)).
  rewrite <- (dpath_change_transport (P := fun x => GDom (P x)) (pR θ)
    (f_equal (G (n2 θ)) (nth_lmap G1 l θ)) (nth_lmap G2 (lmap G1 l) θ)).
  rewrite 2 dpath_change_map, 2 f_equal_compose.
  cbn [f_equal].
  rewrite <- (dpath_change_id (P := fun x => GDom (P x)) HK).
  rewrite 4 dpath_change_comp.
  now apply (dpath_change_cell (P := fun x => GDom (P x))).
Defined.

End Triangle.

(** [ext2] restated over [nth_dpath]: two parallel dependent layer paths are
    equal as soon as their components are. *)
Lemma layer_dpath2_eq {T} {Bd: T -> arity -> HGpd} {d1 d2: T} {e1 e2: d1 = d2}
  {κ: e1 = e2} {l: Layer (Bd d1)} {l': Layer (Bd d2)}
  (u: rew [fun d => Layer (Bd d)] e1 in l = l')
  (v: rew [fun d => Layer (Bd d)] e2 in l = l'):
  (forall ω, rew [fun e => rew [fun d => Bd d ω] e in nth l ω = nth l' ω] κ in
             nth_dpath u ω = nth_dpath v ω) ->
  rew [fun e => rew [fun d => Layer (Bd d)] e in l = l'] κ in u = v.
Proof.
  intro H. apply ext2. intro ω.
  pose proof (eq_sym (map_subst (fun e q => @nth_dpath T Bd d1 d2 e l l' q ω)
    κ u) • H ω) as E.
  unfold nth_dpath in E.
  now exact (eq_sym (eq_trans_sym_cancel_l _ _) •
    (f_equal (fun h => eq_sym (eq_sym (nth_rew e2 l ω)) • h) E •
      eq_trans_sym_cancel_l _ _)).
Defined.

Section Hexagon.

Context {TU T XU X: Type}
        {S: XU -> HGpd} {uf0: arity -> TU -> XU}
        {P: X -> HGpd} {rf0: arity -> T -> X}
        {fA fB fC: TU -> T}
        {B BP BQ BR: arity -> HGpd} {l: Layer B}
        {u0 u1 u2 u3 u4 u5: TU}
        {eU1: u0 = u1} {eU2: u2 = u3} {eU3: u4 = u5}
        {e2: fA u1 = fB u2} {e4: fA u0 = fC u4} {e6: fC u5 = fB u3}
        {P2: forall ω, B ω -> BP ω}
        {Q2: forall ω, B ω -> BQ ω}
        {R2: forall ω, B ω -> BR ω}
        {P1: forall ω, BP ω -> S (uf0 ω u0)}
        {Q1: forall ω, BQ ω -> S (uf0 ω u1)}
        {R1: forall ω, BQ ω -> S (uf0 ω u2)}
        {R1': forall ω, BR ω -> S (uf0 ω u3)}
        {W1: forall ω, BP ω -> S (uf0 ω u4)}
        {W1': forall ω, BR ω -> S (uf0 ω u5)}
        {NA: forall dd ω, S (uf0 ω dd) -> P (rf0 ω (fA dd))}
        {NB: forall dd ω, S (uf0 ω dd) -> P (rf0 ω (fB dd))}
        {NC: forall dd ω, S (uf0 ω dd) -> P (rf0 ω (fC dd))}
        {H1: forall ω (a: B ω), rew [fun dd => S (uf0 ω dd)] eU1 in
               P1 ω (P2 ω a) = Q1 ω (Q2 ω a)}
        {H3: forall ω (a: B ω), rew [fun dd => S (uf0 ω dd)] eU2 in
               R1 ω (Q2 ω a) = R1' ω (R2 ω a)}
        {H5: forall ω (a: B ω), rew [fun dd => S (uf0 ω dd)] eU3 in
               W1 ω (P2 ω a) = W1' ω (R2 ω a)}
        {H2: forall ω (a: BQ ω), rew [fun dd => P (rf0 ω dd)] e2 in
               NA u1 ω (Q1 ω a)
               = NB u2 ω (R1 ω a)}
        {H4: forall ω (a: BP ω), rew [fun dd => P (rf0 ω dd)] e4 in
               NA u0 ω (P1 ω a)
               = NC u4 ω (W1 ω a)}
        {H6: forall ω (a: BR ω), rew [fun dd => P (rf0 ω dd)] e6 in
               NC u5 ω (W1' ω a)
               = NB u3 ω (R1' ω a)}
        {κ: f_equal fA eU1 • (e2 • f_equal fB eU2)
            = e4 • (f_equal fC eU3 • e6)}.

Definition lmap2_hex_pointwise ζ: Type :=
  rew [fun e: fA u0 = fB u3 =>
       rew [fun dd => P (rf0 ζ dd)] e in NA u0 ζ (P1 ζ (P2 ζ (nth l ζ)))
       = NB u3 ζ (R1' ζ (R2 ζ (nth l ζ)))] κ in
  (sigT_map_eq (P := fun dd => GDom (S (uf0 ζ dd)))
      (Q := fun dd => GDom (P (rf0 ζ dd))) (fun dd x => NA dd ζ x) (H1 ζ (nth l ζ))
   ⊙[fun dd => GDom (P (rf0 ζ dd))] (H2 ζ (Q2 ζ (nth l ζ))
      ⊙[fun dd => GDom (P (rf0 ζ dd))]
        sigT_map_eq (P := fun dd => GDom (S (uf0 ζ dd)))
          (Q := fun dd => GDom (P (rf0 ζ dd)))
          (fun dd x => NB dd ζ x) (H3 ζ (nth l ζ)))) =
  H4 ζ (P2 ζ (nth l ζ))
  ⊙[fun dd => GDom (P (rf0 ζ dd))] (sigT_map_eq (P := fun dd => GDom (S (uf0 ζ dd)))
        (Q := fun dd => GDom (P (rf0 ζ dd))) (fun dd x => NC dd ζ x) (H5 ζ (nth l ζ))
     ⊙[fun dd => GDom (P (rf0 ζ dd))] H6 ζ (R2 ζ (nth l ζ))).

Lemma lmap2_hex_rew_eq:
  (forall ζ, lmap2_hex_pointwise ζ) ->
  rew [fun e => rew [fun dd => Layer (fun ω => P (rf0 ω dd))] e in
      lmap (NA u0) (lmap P1 (lmap P2 l))
      = lmap (NB u3) (lmap R1' (lmap R2 l))] κ in
  (sigT_map_eq (P := fun dd => (Layer (fun ω => S (uf0 ω dd))).(GDom))
     (Q := fun x => (Layer (fun ω => P (rf0 ω x))).(GDom))
     (f := fA) (fun dd ll => lmap (NA dd) ll)
     (lmap2_rew_eq (P := S) (rf0 := uf0) (E1 := eU1)
        (l := l) (F1 := P2) (F2 := P1) (G1 := Q2) (G2 := Q1) H1)
   ⊙ (lmap2_rew_eq (P := P) (rf0 := rf0) (E1 := e2)
        (l := lmap Q2 l) (F1 := Q1) (F2 := NA u1) (G1 := R1) (G2 := NB u2) H2
      ⊙[fun x => (Layer (fun ω => P (rf0 ω x))).(GDom)]
        sigT_map_eq (P := fun dd => (Layer (fun ω => S (uf0 ω dd))).(GDom))
          (Q := fun x => (Layer (fun ω => P (rf0 ω x))).(GDom))
          (f := fB) (fun dd ll => lmap (NB dd) ll)
          (lmap2_rew_eq (P := S) (rf0 := uf0) (E1 := eU2)
             (l := l) (F1 := Q2) (F2 := R1) (G1 := R2) (G2 := R1') H3)))
  = lmap2_rew_eq (P := P) (rf0 := rf0) (E1 := e4)
      (l := lmap P2 l) (F1 := P1) (F2 := NA u0) (G1 := W1) (G2 := NC u4) H4
    ⊙[fun x => (Layer (fun ω => P (rf0 ω x))).(GDom)]
      (sigT_map_eq (P := fun dd => (Layer (fun ω => S (uf0 ω dd))).(GDom))
         (Q := fun x => (Layer (fun ω => P (rf0 ω x))).(GDom))
         (f := fC) (fun dd ll => lmap (NC dd) ll)
         (lmap2_rew_eq (P := S) (rf0 := uf0) (E1 := eU3)
            (l := l) (F1 := P2) (F2 := W1) (G1 := R2) (G2 := W1') H5)
       ⊙ lmap2_rew_eq (P := P) (rf0 := rf0) (E1 := e6)
           (l := lmap R2 l) (F1 := W1') (F2 := NC u5) (G1 := R1') (G2 := NB u3)
           H6).
Proof.
  intro Hpointwise.
  apply (layer_dpath2_eq (Bd := fun dd ω => P (rf0 ω dd))).
  intro ζ.
  rewrite 4 nth_dpath_trans.
  rewrite 3 (nth_dpath_sigT_map_eq (Bd := fun dd ω => S (uf0 ω dd))
    (Bd' := fun dd ω => P (rf0 ω dd))).
  rewrite 6 nth_dpath_lmap2_rew_eq.
  specialize (Hpointwise ζ).
  rewrite <- (dpath_change_natural (P := fun dd => GDom (P (rf0 ζ dd)))
    _ _ (H2 ζ) (nth_lmap Q2 l ζ)).
  rewrite <- (dpath_change_natural (P := fun dd => GDom (P (rf0 ζ dd)))
    _ _ (H4 ζ) (nth_lmap P2 l ζ)).
  rewrite <- (dpath_change_natural (P := fun dd => GDom (P (rf0 ζ dd)))
    _ _ (H6 ζ) (nth_lmap R2 l ζ)).
  (** Move the computation paths to the six vertices and compose them there. *)
  rewrite 6 dpath_change_map, 12 dpath_change_nest.
  rewrite 6 f_equal_compose, <- 12 eq_trans_assoc.
  (** Only the two exterior endpoint corrections survive the pasting. *)
  rewrite 4 dpath_change_comp.
  now apply (dpath_change_cell (P := fun dd => GDom (P (rf0 ζ dd)))).
Defined.

End Hexagon.

End LayerGpdTheory.

Module SimplicialGpdLayer <: LayerGpdSig.
  Definition arity: Type := unit.
  Definition Layer (B: arity -> HGpd): HGpd := B tt.
  Definition nth {B: arity -> HGpd} (l: Layer B) (ε: arity): B ε :=
    match ε with tt => l end.
  Definition lam {B: arity -> HGpd} (f: forall ε, B ε): Layer B := f tt.
  Definition nth_lam {B: arity -> HGpd} (f: forall ε, B ε) ε:
    nth (lam f) ε = f ε := match ε with tt => eq_refl end.
  Definition ext {B: arity -> HGpd} (l l': Layer B)
    (H: forall ε, nth l ε = nth l' ε): l = l' := H tt.
  Definition ap_nth {B: arity -> HGpd} {l l': Layer B} (p: l = l') ε:
    nth l ε = nth l' ε := f_equal (fun x => nth x ε) p.

  Lemma ap_nth_ext {B: arity -> HGpd} {l l': Layer B}
    (H: forall ε, nth l ε = nth l' ε) ε: ap_nth (ext l l' H) ε = H ε.
  Proof.
    destruct ε. now exact (f_equal_id (H tt)).
  Defined.

  Lemma ext2 {B: arity -> HGpd} {l l': Layer B} (p q: l = l')
    (H: forall ε, ap_nth p ε = ap_nth q ε): p = q.
  Proof.
    now exact (eq_sym (f_equal_id p) • (H tt • f_equal_id q)).
  Defined.
End SimplicialGpdLayer.

Module CubicalGpdLayer <: LayerGpdSig.
  Definition arity: Type := bool.

  Definition Layer (B: arity -> HGpd): HGpd :=
    gsigT (A := B false) (fun _ => B true).

  Definition nth {B: arity -> HGpd} (l: Layer B) (ε: arity): B ε :=
    match ε with false => l.1 | true => l.2 end.
  Definition lam {B: arity -> HGpd} (f: forall ε, B ε): Layer B :=
    (f false; f true).

  Lemma nth_lam {B: arity -> HGpd} (f: forall ε, B ε) ε: nth (lam f) ε = f ε.
  Proof.
    now destruct ε.
  Defined.

  Definition ap_nth {B: arity -> HGpd} {l l': Layer B} (p: l = l') ε:
    nth l ε = nth l' ε := f_equal (fun x => nth x ε) p.

  (** Paths between layers are, pointwise, a pair of paths: an [HSet]. *)
  Definition code {B: arity -> HGpd} (x y: Layer B): HSet :=
    hsigT (A := hpaths (nth x false) (nth y false))
      (fun _ => hpaths (nth x true) (nth y true)).

  Definition encode {B: arity -> HGpd} {x y: Layer B} (p: x = y): code x y :=
    (ap_nth p false; ap_nth p true).

  Definition decode {B: arity -> HGpd} {x y: Layer B} (c: code x y): x = y :=
    f_equal (fun a => (a; nth x true)) c.1
    • f_equal (fun b => (nth y false; b)) c.2.

  Lemma decode_encode {B: arity -> HGpd} {x y: Layer B} (p: x = y):
    decode (encode p) = p.
  Proof.
    now destruct p.
  Defined.

  Lemma ext {B: arity -> HGpd} (l l': Layer B):
    (forall ε, nth l ε = nth l' ε) -> l = l'.
  Proof.
    intro H. now exact (decode (H false; H true)).
  Defined.

  Lemma encode_decode {B: arity -> HGpd} {x y: Layer B} (c: code x y):
    encode (decode c) = c.
  Proof.
    destruct x as [x1 x2], y as [y1 y2], c as [c1 c2]; cbn in *.
    now destruct c1, c2.
  Defined.

  Lemma ap_nth_ext {B: arity -> HGpd} {l l': Layer B}
    (H: forall ε, nth l ε = nth l' ε) ε: ap_nth (ext l l' H) ε = H ε.
  Proof.
    destruct ε.
    - now exact (f_equal (fun z: code l l' => z.2)
        (encode_decode (H false; H true))).
    - now exact (f_equal (fun z: code l l' => z.1)
        (encode_decode (H false; H true))).
  Defined.

  Lemma ext2 {B: arity -> HGpd} {l l': Layer B} (p q: l = l'):
    (forall ε, ap_nth p ε = ap_nth q ε) -> p = q.
  Proof.
    intro H.
    rewrite <- (decode_encode p), <- (decode_encode q).
    unfold encode, decode; cbn.
    now rewrite (H false), (H true).
  Defined.
End CubicalGpdLayer.
