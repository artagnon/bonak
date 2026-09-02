Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet νGpd.HGpd Notation RewLemmas.

Set Primitive Projections.
Set Printing Projections.

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

Definition lmap2_chain {B B1 B2: arity -> HGpd} {l: Layer B}
  {F1: forall ω, B ω -> B1 ω} {F2: forall ω, B1 ω -> P (rf0 ω d1)}
  {G1: forall ω, B ω -> B2 ω} {G2: forall ω, B2 ω -> P (rf0 ω d2)}
  (H: forall ω, rew [fun d => P (rf0 ω d)] E1 in F2 ω (F1 ω (nth l ω))
                = G2 ω (G1 ω (nth l ω))) ω:
  nth (rew [fun d => Layer (fun ω => P (rf0 ω d))] E1 in lmap F2 (lmap F1 l)) ω
  = nth (lmap G2 (lmap G1 l)) ω :=
  nth_rew (B := fun d ω => P (rf0 ω d)) E1 (lmap F2 (lmap F1 l)) ω
  • (f_equal (fun x => rew [fun d => P (rf0 ω d)] E1 in x)
       (nth_lmap F2 (lmap F1 l) ω)
     • (f_equal (fun x => rew [fun d => P (rf0 ω d)] E1 in F2 ω x)
          (nth_lmap F1 l ω)
        • (H ω
           • (eq_sym (f_equal (G2 ω) (nth_lmap G1 l ω))
              • eq_sym (nth_lmap G2 (lmap G1 l) ω))))).

Definition lmap2_rew_eq {B B1 B2: arity -> HGpd} {l: Layer B}
  {F1: forall ω, B ω -> B1 ω} {F2: forall ω, B1 ω -> P (rf0 ω d1)}
  {G1: forall ω, B ω -> B2 ω} {G2: forall ω, B2 ω -> P (rf0 ω d2)}
  (H: forall ω, rew [fun d => P (rf0 ω d)] E1 in F2 ω (F1 ω (nth l ω))
                = G2 ω (G1 ω (nth l ω))):
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

(** [nth_dpath] undoes [lmap2_rew_eq]: the components of the bridge's output
    are the components it was given, conjugated by the four [nth_lmap]
    corrections that peel the two layer maps on each side. *)
Lemma nth_dpath_lmap2_rew_eq {T X: Type} {P: X -> HGpd} {rf0: arity -> T -> X}
  {d1 d2: T} {E1: d1 = d2} {B B1 B2: arity -> HGpd} {l: Layer B}
  {F1: forall ω, B ω -> B1 ω} {F2: forall ω, B1 ω -> P (rf0 ω d1)}
  {G1: forall ω, B ω -> B2 ω} {G2: forall ω, B2 ω -> P (rf0 ω d2)}
  (H: forall ω, rew [fun d => P (rf0 ω d)] E1 in F2 ω (F1 ω (nth l ω))
                = G2 ω (G1 ω (nth l ω))) ω:
  nth_dpath (Bd := fun d ω => P (rf0 ω d))
    (lmap2_rew_eq (P := P) (rf0 := rf0) (E1 := E1) H) ω
  = f_equal (fun x => rew [fun d => P (rf0 ω d)] E1 in x)
      (nth_lmap F2 (lmap F1 l) ω)
    • (f_equal (fun x => rew [fun d => P (rf0 ω d)] E1 in F2 ω x)
         (nth_lmap F1 l ω)
       • (H ω
          • (eq_sym (f_equal (G2 ω) (nth_lmap G1 l ω))
             • eq_sym (nth_lmap G2 (lmap G1 l) ω)))).
Proof.
  unfold nth_dpath, lmap2_rew_eq.
  rewrite ap_nth_ext.
  unfold lmap2_chain.
  now exact (eq_trans_sym_cancel_l
    (nth_rew (B := fun d ω => P (rf0 ω d)) E1 (lmap F2 (lmap F1 l)) ω) _).
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
  destruct p; destruct q; destruct p'; destruct q'; cbn.
  now unfold nth_dpath; cbn.
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
  = f_equal (fun x => rew [fun d => GDom (Bd' d ω)] f_equal f p in x)
      (nth_lmap (G d1) l ω)
    • (sigT_map_eq (P := fun d => GDom (Bd d ω))
                   (Q := fun d => GDom (Bd' d ω))
                   (fun a x => G a ω x) (nth_dpath q ω)
       • eq_sym (nth_lmap (G d2) l' ω)).
Proof.
  destruct p; destruct q; cbn.
  unfold nth_dpath; cbn.
  now destruct (nth_lmap (G d1) l ω).
Defined.

(** [nth_dpath] of the first projection of a dependent pair path: projecting
    a painting pair path onto a component of its layer part gives the
    component path, up to the [rew_map] cast on the transport. *)
Lemma nth_dpath_sigT_fst {T X: Type} {P: X -> HGpd} {rf0: arity -> T -> X}
  {θ: arity}
  {R: forall d, Layer (fun ω => P (rf0 ω d)) -> HGpd}
  {d1 d2: T} {H: d1 = d2}
  {l1: Layer (fun ω => P (rf0 ω d1))} {l2: Layer (fun ω => P (rf0 ω d2))}
  {Hu: rew [fun d => Layer (fun ω => P (rf0 ω d))] H in l1 = l2}
  {v1: R d1 l1} {v2: R d2 l2}
  (Hv: rew [fun z: {d: T &T Layer (fun ω => P (rf0 ω d))} => (R z.1 z.2).(GDom)]
    (= H; Hu) in
    (v1: (fun z: {d: T &T Layer (fun ω => P (rf0 ω d))} => (R z.1 z.2).(GDom))
      (d1; l1)) = v2):
  sigT_map_eq
    (P := fun d => {a: Layer (fun ω => P (rf0 ω d)) &T R d a})
    (Q := fun x => (P x).(GDom)) (f := fun d => rf0 θ d)
    (fun d X => nth X.1 θ)
    (eq_existT_curried_dep
       (Q := fun z: {d: T &T Layer (fun ω => P (rf0 ω d))} => (R z.1 z.2).(GDom))
       (H := H) (Hu := Hu) (Hv := Hv))
  = eq_sym (rew_map P (rf0 θ) H (nth l1 θ))
    • nth_dpath (Bd := fun d ω => P (rf0 ω d)) Hu θ.
Proof.
  destruct H, Hu, Hv; cbn.
  now unfold nth_dpath; cbn.
Defined.

Lemma sigT_fst_lmap2_rew_eq {T X: Type} {P: X -> HGpd} {rf0: arity -> T -> X}
  {θ: arity}
  {R: forall d, Layer (fun ω => P (rf0 ω d)) -> HGpd}
  {d1 d2: T} {H: d1 = d2}
  {B B1 B2: arity -> HGpd} {l: Layer B}
  {F1: forall ω, B ω -> B1 ω} {F2: forall ω, B1 ω -> P (rf0 ω d1)}
  {G1: forall ω, B ω -> B2 ω} {G2: forall ω, B2 ω -> P (rf0 ω d2)}
  {HL: forall ω, rew [fun d => P (rf0 ω d)] H in F2 ω (F1 ω (nth l ω))
                 = G2 ω (G1 ω (nth l ω))}
  {v1: R d1 (lmap F2 (lmap F1 l))} {v2: R d2 (lmap G2 (lmap G1 l))}
  (Hv: rew [fun z: {d: T &T Layer (fun ω => P (rf0 ω d))} => (R z.1 z.2).(GDom)]
    (= H; lmap2_rew_eq (P := P) (rf0 := rf0) (E1 := H) HL) in
    (v1: (fun z: {d: T &T Layer (fun ω => P (rf0 ω d))} => (R z.1 z.2).(GDom))
      (d1; lmap F2 (lmap F1 l))) = v2):
  sigT_map_eq
    (P := fun d => {a: Layer (fun ω => P (rf0 ω d)) &T R d a})
    (Q := fun x => (P x).(GDom)) (f := fun d => rf0 θ d)
    (fun d X => nth X.1 θ)
    (eq_existT_curried_dep
       (Q := fun z: {d: T &T Layer (fun ω => P (rf0 ω d))} => (R z.1 z.2).(GDom))
       (H := H) (Hu := lmap2_rew_eq (P := P) (rf0 := rf0) (E1 := H) HL)
       (Hv := Hv))
  = eq_sym (rew_map P (rf0 θ) H (nth (lmap F2 (lmap F1 l)) θ))
    • (f_equal (fun x => rew [fun d => P (rf0 θ d)] H in x)
         (nth_lmap F2 (lmap F1 l) θ)
       • (f_equal (fun x => rew [fun d => P (rf0 θ d)] H in F2 θ x)
            (nth_lmap F1 l θ)
          • (HL θ
             • (eq_sym (f_equal (G2 θ) (nth_lmap G1 l θ))
                • eq_sym (nth_lmap G2 (lmap G1 l) θ))))).
Proof.
  rewrite (nth_dpath_sigT_fst (l1 := lmap F2 (lmap F1 l))
    (l2 := lmap G2 (lmap G1 l))
    (Hu := lmap2_rew_eq (P := P) (rf0 := rf0) (E1 := H) HL)
    (v1 := v1) (v2 := v2)).
  now rewrite nth_dpath_lmap2_rew_eq.
Defined.

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
  destruct κ; cbn. intro H. apply ext2; intro ω.
  specialize (H ω). unfold nth_dpath in H.
  revert H. destruct (nth_rew e1 l ω).
  now rewrite 2 eq_trans_refl_l.
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
        {H1: forall ω, rew [fun dd => S (uf0 ω dd)] eU1 in
               P1 ω (P2 ω (nth l ω)) = Q1 ω (Q2 ω (nth l ω))}
        {H3: forall ω, rew [fun dd => S (uf0 ω dd)] eU2 in
               R1 ω (Q2 ω (nth l ω)) = R1' ω (R2 ω (nth l ω))}
        {H5: forall ω, rew [fun dd => S (uf0 ω dd)] eU3 in
               W1 ω (P2 ω (nth l ω)) = W1' ω (R2 ω (nth l ω))}
        {H2: forall ω, rew [fun dd => P (rf0 ω dd)] e2 in
               NA u1 ω (Q1 ω (nth (lmap Q2 l) ω))
               = NB u2 ω (R1 ω (nth (lmap Q2 l) ω))}
        {H4: forall ω, rew [fun dd => P (rf0 ω dd)] e4 in
               NA u0 ω (P1 ω (nth (lmap P2 l) ω))
               = NC u4 ω (W1 ω (nth (lmap P2 l) ω))}
        {H6: forall ω, rew [fun dd => P (rf0 ω dd)] e6 in
               NC u5 ω (W1' ω (nth (lmap R2 l) ω))
               = NB u3 ω (R1' ω (nth (lmap R2 l) ω))}
        {κ: f_equal fA eU1 • (e2 • f_equal fB eU2)
            = e4 • (f_equal fC eU3 • e6)}.

Definition lmap2_hex_pointwise ζ: Type :=
  rew [fun e: fA u0 = fB u3 =>
       rew [fun dd => P (rf0 ζ dd)] e in
       nth (lmap (NA u0) (lmap P1 (lmap P2 l))) ζ
       = nth (lmap (NB u3) (lmap R1' (lmap R2 l))) ζ] κ in
  (f_equal (fun x => rew [fun dd => P (rf0 ζ dd)] f_equal fA eU1 in x)
     (nth_lmap (NA u0) (lmap P1 (lmap P2 l)) ζ)
   • (sigT_map_eq (P := fun a => (S (uf0 ζ a)).(GDom))
        (Q := fun x => (P (rf0 ζ x)).(GDom)) (f := fA) (fun a x => NA a ζ x)
        (f_equal (fun x => rew [fun dd => S (uf0 ζ dd)] eU1 in x)
           (nth_lmap P1 (lmap P2 l) ζ)
         • (f_equal (fun x => rew [fun dd => S (uf0 ζ dd)] eU1 in P1 ζ x)
              (nth_lmap P2 l ζ)
            • (H1 ζ
               • (eq_sym (f_equal (Q1 ζ) (nth_lmap Q2 l ζ))
                  • eq_sym (nth_lmap Q1 (lmap Q2 l) ζ)))))
      • eq_sym (nth_lmap (NA u1) (lmap Q1 (lmap Q2 l)) ζ))
   ⊙[fun dd => (P (rf0 ζ dd)).(GDom)]
     (f_equal (fun x => rew [fun dd => P (rf0 ζ dd)] e2 in x)
        (nth_lmap (NA u1) (lmap Q1 (lmap Q2 l)) ζ)
      • (f_equal (fun x => rew [fun dd => P (rf0 ζ dd)] e2 in NA u1 ζ x)
           (nth_lmap Q1 (lmap Q2 l) ζ)
         • (H2 ζ
            • (eq_sym (f_equal (NB u2 ζ) (nth_lmap R1 (lmap Q2 l) ζ))
               • eq_sym (nth_lmap (NB u2) (lmap R1 (lmap Q2 l)) ζ))))
      ⊙[fun dd => (P (rf0 ζ dd)).(GDom)]
        (f_equal (fun x => rew [fun dd => P (rf0 ζ dd)] f_equal fB eU2 in x)
           (nth_lmap (NB u2) (lmap R1 (lmap Q2 l)) ζ)
         • (sigT_map_eq (P := fun a => (S (uf0 ζ a)).(GDom))
              (Q := fun x => (P (rf0 ζ x)).(GDom)) (f := fB)
              (fun a x => NB a ζ x)
              (f_equal (fun x => rew [fun dd => S (uf0 ζ dd)] eU2 in x)
                 (nth_lmap R1 (lmap Q2 l) ζ)
               • (f_equal
                    (fun x => rew [fun dd => S (uf0 ζ dd)] eU2 in R1 ζ x)
                    (nth_lmap Q2 l ζ)
                  • (H3 ζ
                     • (eq_sym (f_equal (R1' ζ) (nth_lmap R2 l ζ))
                        • eq_sym (nth_lmap R1' (lmap R2 l) ζ)))))
            • eq_sym (nth_lmap (NB u3) (lmap R1' (lmap R2 l)) ζ))))) =
  f_equal (fun x => rew [fun dd => P (rf0 ζ dd)] e4 in x)
    (nth_lmap (NA u0) (lmap P1 (lmap P2 l)) ζ)
  • (f_equal (fun x => rew [fun dd => P (rf0 ζ dd)] e4 in NA u0 ζ x)
       (nth_lmap P1 (lmap P2 l) ζ)
     • (H4 ζ
        • (eq_sym (f_equal (NC u4 ζ) (nth_lmap W1 (lmap P2 l) ζ))
           • eq_sym (nth_lmap (NC u4) (lmap W1 (lmap P2 l)) ζ))))
  ⊙[fun dd => (P (rf0 ζ dd)).(GDom)]
    (f_equal (fun x => rew [fun dd => P (rf0 ζ dd)] f_equal fC eU3 in x)
       (nth_lmap (NC u4) (lmap W1 (lmap P2 l)) ζ)
     • (sigT_map_eq (P := fun a => (S (uf0 ζ a)).(GDom))
          (Q := fun x => (P (rf0 ζ x)).(GDom)) (f := fC)
          (fun a x => NC a ζ x)
          (f_equal (fun x => rew [fun dd => S (uf0 ζ dd)] eU3 in x)
             (nth_lmap W1 (lmap P2 l) ζ)
           • (f_equal (fun x => rew [fun dd => S (uf0 ζ dd)] eU3 in W1 ζ x)
                (nth_lmap P2 l ζ)
              • (H5 ζ
                 • (eq_sym (f_equal (W1' ζ) (nth_lmap R2 l ζ))
                    • eq_sym (nth_lmap W1' (lmap R2 l) ζ)))))
        • eq_sym (nth_lmap (NC u5) (lmap W1' (lmap R2 l)) ζ))
     ⊙[fun dd => (P (rf0 ζ dd)).(GDom)]
       (f_equal (fun x => rew [fun dd => P (rf0 ζ dd)] e6 in x)
          (nth_lmap (NC u5) (lmap W1' (lmap R2 l)) ζ)
        • (f_equal (fun x => rew [fun dd => P (rf0 ζ dd)] e6 in NC u5 ζ x)
             (nth_lmap W1' (lmap R2 l) ζ)
           • (H6 ζ
              • (eq_sym (f_equal (NB u3 ζ) (nth_lmap R1' (lmap R2 l) ζ))
                 • eq_sym (nth_lmap (NB u3) (lmap R1' (lmap R2 l)) ζ)))))).

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
  now exact (Hpointwise ζ).
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
