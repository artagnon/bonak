Set Warnings "-notation-overridden".
From Bonak Require Import SigT Notation RewLemmas νGpd.Pasting.

Set Keyed Unification.

Local Arguments rew_cohLayer_hex {T1 T2 T3 X} P {S2 S3} rf0 {rfF rfG} F G
  {d1 d2} E1 {m1 m2} C2 {n1 n2} D2 C1 D1 K aL aR _ _.

Lemma eq_existT_curried_hex {A1 A2 A3 B: Type}
  {P1: A1 -> Type} {P2: A2 -> Type} {P3: A3 -> Type} {Q: B -> Type}
  (f1: A1 -> B) (g1: forall a, P1 a -> Q (f1 a))
  (f2: A2 -> B) (g2: forall a, P2 a -> Q (f2 a))
  (f3: A3 -> B) (g3: forall a, P3 a -> Q (f3 a))
  {x1 y1: A1} {u1: P1 x1} {v1: P1 y1}
  {x2 y2: A2} {u2: P2 x2} {v2: P2 y2}
  {x3 y3: A3} {u3: P3 x3} {v3: P3 y3}
  {K1: x1 = y1} {W1: rew [P1] K1 in u1 = v1}
  {K2: x2 = y2} {W2: rew [P2] K2 in u2 = v2}
  {K3: x3 = y3} {W3: rew [P3] K3 in u3 = v3}
  {H2: f1 y1 = f3 x3} {U2: rew [Q] H2 in g1 y1 v1 = g3 x3 u3}
  {H1': f1 x1 = f2 x2} {U1': rew [Q] H1' in g1 x1 u1 = g2 x2 u2}
  {H3': f2 y2 = f3 y3} {U3': rew [Q] H3' in g2 y2 v2 = g3 y3 v3}
  (HH: f_equal f1 K1 • (H2 • f_equal f3 K3) =
    H1' • (f_equal f2 K2 • H3'))
  (HHu: rew [fun h => rew [Q] h in g1 x1 u1 = g3 y3 v3] HH in
    (sigT_map_eq g1 W1 ⊙ (U2 ⊙ sigT_map_eq g3 W3)) =
    U1' ⊙ (sigT_map_eq g2 W2 ⊙ U3')):
  f_equal (fun z: {a: A1 &T P1 a} => (f1 z.1; g1 z.1 z.2)) (= K1; W1)
  • ((= H2; U2)
     • f_equal (fun z: {a: A3 &T P3 a} => (f3 z.1; g3 z.1 z.2)) (= K3; W3)) =
  (= H1'; U1')
  • (f_equal (fun z: {a: A2 &T P2 a} => (f2 z.1; g2 z.1 z.2)) (= K2; W2)
     • (= H3'; U3')).
Proof.
  refine (_ • (eq_existT_curried_eq HH HHu • eq_sym _)).
  - now exact (sigT_path_paste (f_equal_eq_existT_curried f1 g1 K1 W1)
      (sigT_path_paste eq_refl (f_equal_eq_existT_curried f3 g3 K3 W3))).
  - now exact (sigT_path_paste eq_refl
      (sigT_path_paste (f_equal_eq_existT_curried f2 g2 K2 W2) eq_refl)).
Defined.

(** The hexagon first normalizes the left route, compares the resulting
    pair paths, and reverses the right normalization. Its dependent lift
    transports both routes to their normal forms. *)
Lemma eq_existT_curried_dep_hex
  {A0 B: Type} {P0: A0 -> Type} {R0: forall a, P0 a -> Type}
  {P': B -> Type} {R': forall b, P' b -> Type}
  (f1: A0 -> B) (g1: forall a, P0 a -> P' (f1 a))
  (h1: forall a u, R0 a u -> R' (f1 a) (g1 a u))
  (f3: A0 -> B) (g3: forall a, P0 a -> P' (f3 a))
  (h3: forall a u, R0 a u -> R' (f3 a) (g3 a u))
  (f2: A0 -> B) (g2: forall a, P0 a -> P' (f2 a))
  (h2: forall a u, R0 a u -> R' (f2 a) (g2 a u))
  {x0 x1 x2 x3 x1' x2': A0}
  {u0: P0 x0} {v0: R0 x0 u0} {u1: P0 x1} {v1: R0 x1 u1}
  {u2: P0 x2} {v2: R0 x2 u2} {u3: P0 x3} {v3: R0 x3 u3}
  {u1': P0 x1'} {v1': R0 x1' u1'} {u2': P0 x2'} {v2': R0 x2' u2'}
  (H1: x0 = x1) (Hu1: rew [P0] H1 in u0 = u1)
  (Hv1: rew [fun z => R0 z.1 z.2] (=H1; Hu1) in
    (v0: (fun z => R0 z.1 z.2) (x0; u0)) = v1)
  (H2: f1 x1 = f3 x2) (Hu2: rew [P'] H2 in g1 x1 u1 = g3 x2 u2)
  (Hv2: rew [fun z => R' z.1 z.2] (=H2; Hu2) in
    (h1 x1 u1 v1: (fun z => R' z.1 z.2) (f1 x1; g1 x1 u1)) = h3 x2 u2 v2)
  (H3: x2 = x3) (Hu3: rew [P0] H3 in u2 = u3)
  (Hv3: rew [fun z => R0 z.1 z.2] (=H3; Hu3) in
    (v2: (fun z => R0 z.1 z.2) (x2; u2)) = v3)
  (H1': f1 x0 = f2 x1') (Hu1': rew [P'] H1' in g1 x0 u0 = g2 x1' u1')
  (Hv1': rew [fun z => R' z.1 z.2] (=H1'; Hu1') in
    (h1 x0 u0 v0: (fun z => R' z.1 z.2) (f1 x0; g1 x0 u0)) = h2 x1' u1' v1')
  (H2': x1' = x2') (Hu2': rew [P0] H2' in u1' = u2')
  (Hv2': rew [fun z => R0 z.1 z.2] (=H2'; Hu2') in
    (v1': (fun z => R0 z.1 z.2) (x1'; u1')) = v2')
  (H3': f2 x2' = f3 x3) (Hu3': rew [P'] H3' in g2 x2' u2' = g3 x3 u3)
  (Hv3': rew [fun z => R' z.1 z.2] (=H3'; Hu3') in
    (h2 x2' u2' v2': (fun z => R' z.1 z.2) (f2 x2'; g2 x2' u2')) = h3 x3 u3 v3)
  (HH: f_equal f1 H1 • (H2 • f_equal f3 H3) =
    H1' • (f_equal f2 H2' • H3'))
  (HHu: rew [fun h => rew [P'] h in g1 x0 u0 = g3 x3 u3] HH in
    (sigT_map_eq g1 Hu1 ⊙ (Hu2 ⊙ sigT_map_eq g3 Hu3)) =
    Hu1' ⊙ (sigT_map_eq g2 Hu2' ⊙ Hu3'))
  (HHv:
    rew [fun p: (f1 x0; g1 x0 u0) = (f3 x3; g3 x3 u3) =>
        rew [fun z: {a: B &T P' a} => R' z.1 z.2] p in
        (h1 x0 u0 v0:
          (fun z: {a: B &T P' a} => R' z.1 z.2) (f1 x0; g1 x0 u0)) =
        h3 x3 u3 v3]
      eq_existT_curried_hex f1 g1 f2 g2 f3 g3 HH HHu in
    (@sigT_map_eq _ _ (fun z: {x: A0 &T P0 x} => R0 z.1 z.2)
       (fun z: {x: B &T P' x} => R' z.1 z.2)
       (fun z => (f1 z.1; g1 z.1 z.2)) (fun z => h1 z.1 z.2)
       (x0; u0) (x1; u1) v0 v1 (=H1; Hu1) Hv1
     ⊙ (Hv2
        ⊙ @sigT_map_eq _ _ (fun z: {x: A0 &T P0 x} => R0 z.1 z.2)
            (fun z: {x: B &T P' x} => R' z.1 z.2)
            (fun z => (f3 z.1; g3 z.1 z.2)) (fun z => h3 z.1 z.2)
            (x2; u2) (x3; u3) v2 v3 (=H3; Hu3) Hv3)) =
    Hv1'
    ⊙ (@sigT_map_eq _ _ (fun z: {x: A0 &T P0 x} => R0 z.1 z.2)
         (fun z: {x: B &T P' x} => R' z.1 z.2)
         (fun z => (f2 z.1; g2 z.1 z.2)) (fun z => h2 z.1 z.2)
         (x1'; u1') (x2'; u2') v1' v2' (=H2'; Hu2') Hv2' ⊙ Hv3')):
  rew [fun h => rew [fun x => {a: P' x &T R' x a}] h in
      (g1 x0 u0; h1 x0 u0 v0) = (g3 x3 u3; h3 x3 u3 v3)] HH in
  (sigT_map_eq (fun a uv => (g1 a uv.1; h1 a uv.1 uv.2))
     (eq_existT_curried_dep (Q := fun z => R0 z.1 z.2)
        (H := H1) (Hu := Hu1) (Hv := Hv1))
   ⊙ (eq_existT_curried_dep (Q := fun z => R' z.1 z.2)
        (H := H2) (Hu := Hu2) (Hv := Hv2)
      ⊙ sigT_map_eq (fun a uv => (g3 a uv.1; h3 a uv.1 uv.2))
          (eq_existT_curried_dep (Q := fun z => R0 z.1 z.2)
             (H := H3) (Hu := Hu3) (Hv := Hv3)))) =
  eq_existT_curried_dep (Q := fun z => R' z.1 z.2)
    (H := H1') (Hu := Hu1') (Hv := Hv1')
  ⊙ (sigT_map_eq (fun a uv => (g2 a uv.1; h2 a uv.1 uv.2))
       (eq_existT_curried_dep (Q := fun z => R0 z.1 z.2)
          (H := H2') (Hu := Hu2') (Hv := Hv2'))
     ⊙ eq_existT_curried_dep (Q := fun z => R' z.1 z.2)
         (H := H3') (Hu := Hu3') (Hv := Hv3')).
Proof.
  rewrite 3 sigT_map_eq_existT_curried_dep_curried.
  rewrite 4 (sigT_trans_eq_existT_curried_dep (Q := fun z => R' z.1 z.2)).
  refine (eq_existT_curried_dep_eq (Q := fun z => R' z.1 z.2) HH HHu _).
  unfold eq_existT_curried_hex in HHv.
  cbn [projT1 projT2] in HHv |- *.
  pose (R := fun z: {a: B &T P' a} => R' z.1 z.2).
  apply (rew_conjugate (fun p: (f1 x0; g1 x0 u0) = (f3 x3; g3 x3 u3) =>
    @eq_rect _ (f1 x0; g1 x0 u0) R
      (h1 x0 u0 v0) (f3 x3; g3 x3 u3) p = h3 x3 u3 v3)) in HHv.
  rewrite 4 (sigT_path_paste_dep R) in HHv.
  now exact HHv.
Defined.

Section Coh2Layer.

Context {X2 X1 X0: Type}.
Context {S2: X2 -> Type}.
Context {S1: X1 -> Type}.
Context {S0: X0 -> Type}.

Context {TU T: Type}.
Context {uf0: TU -> X1}.
Context {rf0: T -> X0}.
Context {fA fB fC: TU -> T}.

Context {rfq rfs rfr: X1 -> X0}.
Context {Fq: forall y, S1 y -> S0 (rfq y)}.
Context {Fs: forall y, S1 y -> S0 (rfs y)}.
Context {Fr: forall y, S1 y -> S0 (rfr y)}.
Context {gq: forall dd, rfq (uf0 dd) = rf0 (fA dd)}.
Context {gs: forall dd, rfs (uf0 dd) = rf0 (fB dd)}.
Context {gr: forall dd, rfr (uf0 dd) = rf0 (fC dd)}.

Context {rur rus ruq1 rur1: X2 -> X1}.
Context {Rr: forall z, S2 z -> S1 (rur z)}.
Context {Rs: forall z, S2 z -> S1 (rus z)}.
Context {Rq1: forall z, S2 z -> S1 (ruq1 z)}.
Context {Rr1: forall z, S2 z -> S1 (rur1 z)}.

Context {KA2: forall z, rfq (rus z) = rfs (ruq1 z)}.
Context {KA4: forall z, rfq (rur z) = rfr (ruq1 z)}.
Context {KA6: forall z, rfr (rus z) = rfs (rur1 z)}.
Context {HKA2: forall z (c: S2 z),
  rew [S0] KA2 z in Fq (rus z) (Rs z c) = Fs (ruq1 z) (Rq1 z c)}.
Context {HKA4: forall z (c: S2 z),
  rew [S0] KA4 z in Fq (rur z) (Rr z c) = Fr (ruq1 z) (Rq1 z c)}.
Context {HKA6: forall z (c: S2 z),
  rew [S0] KA6 z in Fr (rus z) (Rs z c) = Fs (rur1 z) (Rr1 z c)}.

(** The permutahedral coherence of frames compares four hexagons on each
    side. The squares [NKA2, NKA4, NKA6] express naturality of the restriction
    coherences; [Ngq, Ngs, Ngr] express naturality of the comparison maps.
    Each side-face pasting combines one hexagon and one of these squares.
    Pasting [HHA] at the top and the image of [κ] at the bottom completes
    the two boundary paths. *)
Definition permutahedral_coherence
  (u0 u1 u2 u3 u4 u5: TU)
  (eU1: u0 = u1) (eU2: u2 = u3) (eU3: u4 = u5)
  (e2: fA u1 = fB u2) (e4: fA u0 = fC u4) (e6: fC u5 = fB u3)
  (zs1 zs2 zr1 zr2 zq1 zq2: X2)
  (pIs: zs1 = zs2) (pIr: zr1 = zr2) (pIq: zq1 = zq2)
  (pV0: rur zs2 = uf0 u0) (pV1: rus zr2 = uf0 u1)
  (pV2: ruq1 zr2 = uf0 u2) (pV3: rur1 zq2 = uf0 u3)
  (pV4: ruq1 zs2 = uf0 u4) (pV5: rus zq2 = uf0 u5)
  (K1: rur zs1 = rus zr1) (K3: ruq1 zr1 = rur1 zq1) (K5: ruq1 zs1 = rus zq1)
  (HH1: f_equal rur pIs • (pV0 • f_equal uf0 eU1)
        = K1 • (f_equal rus pIr • pV1))
  (HH3: f_equal ruq1 pIr • (pV2 • f_equal uf0 eU2)
        = K3 • (f_equal rur1 pIq • pV3))
  (HH5: f_equal ruq1 pIs • (pV4 • f_equal uf0 eU3)
        = K5 • (f_equal rus pIq • pV5))
  (κ: f_equal fA eU1 • (e2 • f_equal fB eU2)
      = e4 • (f_equal fC eU3 • e6))
  (HH2: f_equal rfq pV1 • (gq u1 • f_equal rf0 e2)
        = KA2 zr2 • (f_equal rfs pV2 • gs u2))
  (HH4: f_equal rfq pV0 • (gq u0 • f_equal rf0 e4)
        = KA4 zs2 • (f_equal rfr pV4 • gr u4))
  (HH6: f_equal rfr pV5 • (gr u5 • f_equal rf0 e6)
        = KA6 zq2 • (f_equal rfs pV3 • gs u3))
  (HHA: f_equal rfq K1 • (KA2 zr1 • f_equal rfs K3)
      = KA4 zs1 • (f_equal rfr K5 • KA6 zq1)): Type :=
  let NKA2: f_equal rfq (f_equal rus pIr) • KA2 zr2 =
      KA2 zr1 • f_equal rfs (f_equal ruq1 pIr) :=
    f_equal_naturality rus ruq1 rfq rfs KA2 pIr in
  let NKA4: f_equal rfq (f_equal rur pIs) • KA4 zs2 =
      KA4 zs1 • f_equal rfr (f_equal ruq1 pIs) :=
    f_equal_naturality rur ruq1 rfq rfr KA4 pIs in
  let NKA6: f_equal rfr (f_equal rus pIq) • KA6 zq2 =
      KA6 zq1 • f_equal rfs (f_equal rur1 pIq) :=
    f_equal_naturality rus rur1 rfr rfs KA6 pIq in
  let Ngq: f_equal rfq (f_equal uf0 eU1) • gq u1 =
      gq u0 • f_equal rf0 (f_equal fA eU1) :=
    f_equal_naturality uf0 fA rfq rf0 gq eU1 in
  let Ngs: f_equal rfs (f_equal uf0 eU2) • gs u3 =
      gs u2 • f_equal rf0 (f_equal fB eU2) :=
    f_equal_naturality uf0 fB rfs rf0 gs eU2 in
  let Ngr: f_equal rfr (f_equal uf0 eU3) • gr u5 =
      gr u4 • f_equal rf0 (f_equal fC eU3) :=
    f_equal_naturality uf0 fC rfr rf0 gr eU3 in
  let left := square_compose_map rf0
      (layer_square_map uf0 rur rus rfq fA rf0 gq eU1 pIs pIr pV0 pV1 K1 HH1 Ngq)
      (square_compose_map rf0
        (layer_square_nat rus ruq1 rfq rfs rf0 KA2 pIr pV1 pV2 e2 (gq u1) (gs u2) HH2 NKA2)
        (layer_square_map uf0 ruq1 rur1 rfs fB rf0 gs eU2 pIr pIq pV2 pV3 K3 HH3 Ngs)) •
    whisker_r HHA _ in
  let right := whisker_l _ (f_equal (fun e => f_equal rf0 e) κ) •
    square_compose_map rf0
      (layer_square_nat rur ruq1 rfq rfr rf0 KA4 pIs pV0 pV4 e4 (gq u0) (gr u4) HH4 NKA4)
      (square_compose_map rf0
        (layer_square_map uf0 ruq1 rus rfr fC rf0 gr eU3 pIs pIq pV4 pV5 K5 HH5 Ngr)
        (layer_square_nat rus rur1 rfr rfs rf0 KA6 pIq pV5 pV3 e6 (gr u5) (gs u3) HH6 NKA6)) in
  left = right.


(** The dependent hexagon transported through the six layer-coherence cells.
    The frame premise [permutahedral_coherence] compares its two boundary pastings. *)
Lemma rew_coh2Layer_perm4
  (u0 u1 u2 u3 u4 u5: TU)
  (eU1: u0 = u1) (eU2: u2 = u3) (eU3: u4 = u5)
  (e2: fA u1 = fB u2) (e4: fA u0 = fC u4) (e6: fC u5 = fB u3)
  (zs1 zs2 zr1 zr2 zq1 zq2: X2)
  (pIs: zs1 = zs2) (pIr: zr1 = zr2) (pIq: zq1 = zq2)
  (aS: S2 zs1) (aR: S2 zr1) (aQ: S2 zq1)
  (pV0: rur zs2 = uf0 u0) (pV1: rus zr2 = uf0 u1)
  (pV2: ruq1 zr2 = uf0 u2) (pV3: rur1 zq2 = uf0 u3)
  (pV4: ruq1 zs2 = uf0 u4) (pV5: rus zq2 = uf0 u5)
  (K1: rur zs1 = rus zr1) (K3: ruq1 zr1 = rur1 zq1) (K5: ruq1 zs1 = rus zq1)
  (HK1: rew [S1] K1 in Rr zs1 aS = Rs zr1 aR)
  (HK3: rew [S1] K3 in Rq1 zr1 aR = Rr1 zq1 aQ)
  (HK5: rew [S1] K5 in Rq1 zs1 aS = Rs zq1 aQ)
  (HH1: f_equal rur pIs • (pV0 • f_equal uf0 eU1)
        = K1 • (f_equal rus pIr • pV1))
  (HH3: f_equal ruq1 pIr • (pV2 • f_equal uf0 eU2)
        = K3 • (f_equal rur1 pIq • pV3))
  (HH5: f_equal ruq1 pIs • (pV4 • f_equal uf0 eU3)
        = K5 • (f_equal rus pIq • pV5))
  (κ: f_equal fA eU1 • (e2 • f_equal fB eU2)
      = e4 • (f_equal fC eU3 • e6))
  (HH2: f_equal rfq pV1 • (gq u1 • f_equal rf0 e2)
        = KA2 zr2 • (f_equal rfs pV2 • gs u2))
  (HH4: f_equal rfq pV0 • (gq u0 • f_equal rf0 e4)
        = KA4 zs2 • (f_equal rfr pV4 • gr u4))
  (HH6: f_equal rfr pV5 • (gr u5 • f_equal rf0 e6)
        = KA6 zq2 • (f_equal rfs pV3 • gs u3))
  (HHA: f_equal rfq K1 • (KA2 zr1 • f_equal rfs K3)
        = KA4 zs1 • (f_equal rfr K5 • KA6 zq1))
  (Hcoh2Painting:
    rew [fun π: rfq (rur zs1) = rfs (rur1 zq1) =>
        rew [S0] π in Fq (rur zs1) (Rr zs1 aS)
        = Fs (rur1 zq1) (Rr1 zq1 aQ)] HHA in
    (sigT_map_eq Fq HK1 ⊙ (HKA2 zr1 aR ⊙ sigT_map_eq Fs HK3)) =
    HKA4 zs1 aS ⊙ (sigT_map_eq Fr HK5 ⊙ HKA6 zq1 aQ))
  (Hcoh3Frame: permutahedral_coherence u0 u1 u2 u3 u4 u5
    eU1 eU2 eU3 e2 e4 e6 zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq
    pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5 HH1 HH3 HH5 κ HH2 HH4 HH6 HHA):
  rew [fun e: fA u0 = fB u3 =>
    rew [fun dd => S0 (rf0 dd)] e in
      rew [S0] gq u0 in Fq (uf0 u0)
        (rew [S1] pV0 in Rr zs2 (rew [S2] pIs in aS)) =
      rew [S0] gs u3 in Fs (uf0 u3)
        (rew [S1] pV3 in Rr1 zq2 (rew [S2] pIq in aQ))] κ in
  (sigT_map_eq (fun dd x => rew [S0] gq dd in Fq (uf0 dd) x)
     (rew_cohLayer_hex S1 uf0 Rr Rs eU1 pIs pIr pV0 pV1 K1 aS aR HK1 HH1)
   ⊙ (rew_cohLayer_hex S0 rf0 Fq Fs e2 pV1 pV2 (gq u1) (gs u2) (KA2 zr2)
        (Rs zr2 (rew [S2] pIr in aR)) (Rq1 zr2 (rew [S2] pIr in aR))
        (HKA2 zr2 (rew [S2] pIr in aR)) HH2
      ⊙ sigT_map_eq (fun dd x => rew [S0] gs dd in Fs (uf0 dd) x)
          (rew_cohLayer_hex S1 uf0 Rq1 Rr1 eU2 pIr pIq pV2 pV3 K3 aR aQ HK3 HH3))) =
  rew_cohLayer_hex S0 rf0 Fq Fr e4 pV0 pV4 (gq u0) (gr u4) (KA4 zs2)
    (Rr zs2 (rew [S2] pIs in aS)) (Rq1 zs2 (rew [S2] pIs in aS))
    (HKA4 zs2 (rew [S2] pIs in aS)) HH4
  ⊙ (sigT_map_eq (fun dd x => rew [S0] gr dd in Fr (uf0 dd) x)
       (rew_cohLayer_hex S1 uf0 Rq1 Rs eU3 pIs pIq pV4 pV5 K5 aS aQ HK5 HH5)
     ⊙ rew_cohLayer_hex S0 rf0 Fr Fs e6 pV5 pV3 (gr u5) (gs u3) (KA6 zq2)
         (Rs zq2 (rew [S2] pIq in aQ)) (Rr1 zq2 (rew [S2] pIq in aQ))
         (HKA6 zq2 (rew [S2] pIq in aQ)) HH6).
Proof.
  refine (square_cube_map_dep rf0 S0 _ _ κ HHA Hcoh3Frame
    _ _ _ _ _ _ _ _ Hcoh2Painting).
  - eapply square_compose_map_dep.
    + now exact (layer_square_map_dep uf0 rur rus rfq fA rf0 gq S1 S0 S2 S2
        Fq Rr Rs eU1 pIs pIr pV0 pV1 K1 HH1 HK1).
    + eapply square_compose_map_dep.
      * now exact (layer_square_nat_dep rus ruq1 rfq rfs rf0 Rs Rq1 Fq Fs KA2 HKA2
          pIr pV1 pV2 e2 (gq u1) (gs u2) HH2 aR).
      * now exact (layer_square_map_dep uf0 ruq1 rur1 rfs fB rf0 gs S1 S0 S2 S2
          Fs Rq1 Rr1 eU2 pIr pIq pV2 pV3 K3 HH3 HK3).
  - eapply square_compose_map_dep.
    + now exact (layer_square_nat_dep rur ruq1 rfq rfr rf0 Rr Rq1 Fq Fr KA4 HKA4
        pIs pV0 pV4 e4 (gq u0) (gr u4) HH4 aS).
    + eapply square_compose_map_dep.
      * now exact (layer_square_map_dep uf0 ruq1 rus rfr fC rf0 gr S1 S0 S2 S2
          Fr Rq1 Rs eU3 pIs pIq pV4 pV5 K5 HH5 HK5).
      * now exact (layer_square_nat_dep rus rur1 rfr rfs rf0 Rs Rr1 Fr Fs KA6 HKA6
          pIq pV5 pV3 e6 (gr u5) (gs u3) HH6 aQ).
Defined.

End Coh2Layer.

Lemma rew_coh2Painting_restr0 {TU TL: Type}
  {P: TL -> Type} {S: TU -> Type}
  {rq rr r0: TU -> TL}
  (F: forall m, S m -> P (rq m))
  (G: forall n, S n -> P (rr n))
  {d1 d2: TU} (E1: d1 = d2)
  {m1 m2: TU} (e2: m1 = m2)
  {n1 n2: TU} (e5: n1 = n2)
  (pQ: rq m2 = r0 d1) (pR: rr n2 = r0 d2)
  (KA: rq m1 = rr n1)
  (aL: S m1) (aR: S n1)
  (HK: rew [P] KA in F m1 aL = G n1 aR)
  (κ: f_equal rq e2 • (pQ • f_equal r0 E1) = KA • (f_equal rr e5 • pR)):
  rew [fun π: rq m1 = r0 d2 =>
    rew [P] π in F m1 aL = rew [P] pR in G n2 (rew [S] e5 in aR)] κ in
  (sigT_map_eq (Q := P) F (p := e2) (u := aL) eq_refl
   ⊙ (eq_refl
      ⊙ (eq_sym (rew_map P r0 E1 (rew [P] pQ in F m2 (rew [S] e2 in aL)))
         • rew_cohLayer_hex P r0 F G E1 e2 e5 pQ pR KA aL aR HK κ))) =
  HK ⊙ (sigT_map_eq (Q := P) G (p := e5) (u := aR) eq_refl ⊙ eq_refl).
Proof.
  rewrite <- sigT_trans_eq_assoc.
  rewrite rew_compose.
  rewrite <- (sigT_map_eq_id (P := P) r0).
  now exact (layer_square rq rr r0 F G e2 e5 E1 pQ pR KA HK κ).
Defined.
