Set Warnings "-notation-overridden".
From Bonak Require Import SigT Notation RewLemmas.

Set Keyed Unification.

Local Arguments rew_cohLayer33 {T1 T2 T3 X} P {S2 S3} rf0 {rfF rfG} F G
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
  rewrite 3 f_equal_eq_existT_curried.
  rewrite 4 eq_trans_eq_existT_curried.
  now exact (eq_existT_curried_eq HH HHu).
Defined.

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
  revert HHv.
  generalize (eq_existT_curried_eq HH HHu).
  do 4 lazymatch goal with
  | |- context [ @eq_trans_eq_existT_curried ?A ?P ?x ?y ?z ?u ?v ?w
        ?p ?q ?p' ?q' ] =>
      generalize (@eq_trans_eq_existT_curried A P x y z u v w p q p' q')
  end.
  generalize (f_equal_eq_existT_curried f2 g2 H2' Hu2').
  generalize (f_equal_eq_existT_curried f3 g3 H3 Hu3).
  generalize (f_equal_eq_existT_curried f1 g1 H1 Hu1).
  generalize (= f_equal f1 H1; sigT_map_eq g1 Hu1).
  generalize (= f_equal f3 H3; sigT_map_eq g3 Hu3).
  generalize (= f_equal f2 H2'; sigT_map_eq g2 Hu2').
  generalize (= H2 • f_equal f3 H3; Hu2 ⊙ sigT_map_eq g3 Hu3).
  generalize (= f_equal f2 H2' • H3'; sigT_map_eq g2 Hu2' ⊙ Hu3').
  generalize (= f_equal f1 H1 • (H2 • f_equal f3 H3);
    sigT_map_eq g1 Hu1 ⊙ (Hu2 ⊙ sigT_map_eq g3 Hu3)).
  generalize (= H1' • (f_equal f2 H2' • H3');
    Hu1' ⊙ (sigT_map_eq g2 Hu2' ⊙ Hu3')).
  intros qR qL q23' q23 q2' q3 q1 e e0 e1 e2 e3 e4 e5 e6.
  destruct e, e0, e1, e2, e3, e4, e5.
  intros HHv'; now exact HHv'.
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

Context {A0: Type}.
Context {a: A0}.

(** The permutahedral coherence of frames: the hexagon proved as a
    composition of the seven other hexagons of the permutahedron. The six
    squares hold by naturality and don't appear here explicitly. *)
Lemma permutahedral_coherence
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
  (HH2: f_equal rfq pV1 • (gq u1 • f_equal rf0 e2)
        = KA2 zr2 • (f_equal rfs pV2 • gs u2))
  (HH4: f_equal rfq pV0 • (gq u0 • f_equal rf0 e4)
        = KA4 zs2 • (f_equal rfr pV4 • gr u4))
  (HH6: f_equal rfr pV5 • (gr u5 • f_equal rf0 e6)
        = KA6 zq2 • (f_equal rfs pV3 • gs u3))
  (κ: f_equal fA eU1 • (e2 • f_equal fB eU2)
      = e4 • (f_equal fC eU3 • e6)):
  f_equal rfq K1 • (KA2 zr1 • f_equal rfs K3)
  = KA4 zs1 • (f_equal rfr K5 • KA6 zq1).
Proof.
  destruct eU1, eU2, eU3, pIs, pIr, pIq.
  cbn in HH1, HH3, HH5, κ.
  revert K1 K3 K5 pV1 pV3 pV5 pV0 pV2 pV4 HH1 HH3 HH5
    e6 e2 e4 κ HH2 HH4 HH6.
  generalize (KA2 zr1). generalize (KA4 zs1). generalize (KA6 zq1).
  generalize (gq u0). generalize (gs u2). generalize (gr u4).
  generalize (fA u0). generalize (fB u2). generalize (fC u4).
  generalize (uf0 u0). generalize (uf0 u2). generalize (uf0 u4).
  generalize (rur zs1). generalize (rus zr1). generalize (ruq1 zr1).
  generalize (rur1 zq1). generalize (ruq1 zs1). generalize (rus zq1).
  intros t t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 ge gs0 gq0 k6 k4 k2
    K1 K3 K5 pV1 pV3 pV5 pV0 pV2 pV4 HH1 HH3 HH5 e6 e2 e4 κ HH2 HH4 HH6.
  revert ge gs0 gq0 pV0 pV2 pV4 HH1 HH3 HH5 e6 e2 e4 κ HH2 HH4 HH6.
  destruct pV1, pV3, pV5.
  intros ge gs0 gq0 pV0 pV2 pV4 HH1 HH3 HH5.
  cbn in HH1, HH3, HH5.
  destruct HH1, HH3, HH5.
  revert ge gs0 gq0.
  destruct pV0, pV2, pV4.
  intros ge gs0 gq0 e6 e2 e4 κ.
  revert e2 e4 κ ge gs0 gq0.
  destruct e6.
  destruct e2.
  intros e4 κ. cbn in κ. destruct κ.
  intros ge gs0 gq0.
  revert k2 k4 k6.
  revert gs0 ge gq0.
  cbn.
  generalize (rfq t4). generalize (rfs t2). generalize (rfr t0).
  generalize (rf0 t10).
  destruct gs0.
  destruct ge.
  destruct gq0.
  intros k2 k4 k6 HH2 HH4 HH6.
  cbn in HH2, HH4, HH6.
  destruct HH2, HH4, HH6.
  now reflexivity.
Defined.

Lemma rew_coh2Layer
  (u0 u1 u2 u3 u4 u5: TU)
  (eU1: u0 = u1) (eU2: u2 = u3) (eU3: u4 = u5)
  (e2: fA u1 = fB u2) (e4: fA u0 = fC u4) (e6: fC u5 = fB u3)
  (zs1 zs2 zr1 zr2 zq1 zq2: X2)
  (pIs: zs1 = zs2) (pIr: zr1 = zr2) (pIq: zq1 = zq2)
  (FIs: A0 -> S2 zs1) (FIr: A0 -> S2 zr1) (FIq: A0 -> S2 zq1)
  (pV0: rur zs2 = uf0 u0) (pV1: rus zr2 = uf0 u1)
  (pV2: ruq1 zr2 = uf0 u2) (pV3: rur1 zq2 = uf0 u3)
  (pV4: ruq1 zs2 = uf0 u4) (pV5: rus zq2 = uf0 u5)
  (K1: rur zs1 = rus zr1) (K3: ruq1 zr1 = rur1 zq1) (K5: ruq1 zs1 = rus zq1)
  (HK1: rew [S1] K1 in Rr zs1 (FIs a) = Rs zr1 (FIr a))
  (HK3: rew [S1] K3 in Rq1 zr1 (FIr a) = Rr1 zq1 (FIq a))
  (HK5: rew [S1] K5 in Rq1 zs1 (FIs a) = Rs zq1 (FIq a))
  (HH1: f_equal rur pIs • (pV0 • f_equal uf0 eU1)
        = K1 • (f_equal rus pIr • pV1))
  (HH3: f_equal ruq1 pIr • (pV2 • f_equal uf0 eU2)
        = K3 • (f_equal rur1 pIq • pV3))
  (HH5: f_equal ruq1 pIs • (pV4 • f_equal uf0 eU3)
        = K5 • (f_equal rus pIq • pV5))
  (HH2: f_equal rfq pV1 • (gq u1 • f_equal rf0 e2)
        = KA2 zr2 • (f_equal rfs pV2 • gs u2))
  (HH4: f_equal rfq pV0 • (gq u0 • f_equal rf0 e4)
        = KA4 zs2 • (f_equal rfr pV4 • gr u4))
  (HH6: f_equal rfr pV5 • (gr u5 • f_equal rf0 e6)
        = KA6 zq2 • (f_equal rfs pV3 • gs u3))
  (aP: S2 zs2) (kP: aP = rew [S2] pIs in FIs a)
  (aQ: S2 zr2) (kQ: aQ = rew [S2] pIr in FIr a)
  (aR: S2 zq2) (kR: aR = rew [S2] pIq in FIq a)
  (bP: S1 (uf0 u0)) (kbP: bP = rew [S1] pV0 in Rr zs2 aP)
  (bQ: S1 (uf0 u1)) (kbQ: bQ = rew [S1] pV1 in Rs zr2 aQ)
  (bR: S1 (uf0 u2)) (kbR: bR = rew [S1] pV2 in Rq1 zr2 aQ)
  (bR': S1 (uf0 u3)) (kbR': bR' = rew [S1] pV3 in Rr1 zq2 aR)
  (bW: S1 (uf0 u4)) (kbW: bW = rew [S1] pV4 in Rq1 zs2 aP)
  (bW': S1 (uf0 u5)) (kbW': bW' = rew [S1] pV5 in Rs zq2 aR)
  (cA0: S0 (rf0 (fA u0))) (kc0: cA0 = rew [S0] gq u0 in Fq (uf0 u0) bP)
  (cA1: S0 (rf0 (fA u1))) (kc1: cA1 = rew [S0] gq u1 in Fq (uf0 u1) bQ)
  (cB2: S0 (rf0 (fB u2))) (kc2: cB2 = rew [S0] gs u2 in Fs (uf0 u2) bR)
  (cB3: S0 (rf0 (fB u3))) (kc3: cB3 = rew [S0] gs u3 in Fs (uf0 u3) bR')
  (cC4: S0 (rf0 (fC u4))) (kc4: cC4 = rew [S0] gr u4 in Fr (uf0 u4) bW)
  (cC5: S0 (rf0 (fC u5))) (kc5: cC5 = rew [S0] gr u5 in Fr (uf0 u5) bW')
  (κ: f_equal fA eU1 • (e2 • f_equal fB eU2)
      = e4 • (f_equal fC eU3 • e6))
  (HHA: f_equal rfq K1 • (KA2 zr1 • f_equal rfs K3)
        = KA4 zs1 • (f_equal rfr K5 • KA6 zq1))
  (Hcoh2Painting:
    rew [fun π: rfq (rur zs1) = rfs (rur1 zq1) =>
        rew [S0] π in Fq (rur zs1) (Rr zs1 (FIs a))
        = Fs (rur1 zq1) (Rr1 zq1 (FIq a))] HHA in
    (sigT_map_eq Fq HK1 ⊙ (HKA2 zr1 (FIr a) ⊙ sigT_map_eq Fs HK3)) =
    HKA4 zs1 (FIs a) ⊙ (sigT_map_eq Fr HK5 ⊙ HKA6 zq1 (FIq a)))
  (Hcoh3Frame: HHA = permutahedral_coherence u0 u1 u2 u3 u4 u5
    eU1 eU2 eU3 e2 e4 e6 zs1 zs2 zr1 zr2 zq1 zq2 pIs pIr pIq
    pV0 pV1 pV2 pV3 pV4 pV5 K1 K3 K5 HH1 HH3 HH5 HH2 HH4 HH6 κ):
  rew [fun e: fA u0 = fB u3 =>
       rew [fun dd => S0 (rf0 dd)] e in cA0 = cB3] κ in
  (f_equal (fun x => rew [fun dd => S0 (rf0 dd)] f_equal fA eU1 in x) kc0
   • (sigT_map_eq (P := fun dd => S1 (uf0 dd)) (Q := fun dd => S0 (rf0 dd))
        (f := fA) (fun dd x => rew [S0] gq dd in Fq (uf0 dd) x)
        (f_equal (fun x => rew [fun dd => S1 (uf0 dd)] eU1 in x) kbP
         • (f_equal (fun x =>
              rew [fun dd => S1 (uf0 dd)] eU1 in rew [S1] pV0 in Rr zs2 x) kP
            • (rew_cohLayer33 S1 uf0 Rr Rs eU1 pIs pIr pV0 pV1 K1
                 (FIs a) (FIr a) HK1 HH1
               • (eq_sym (f_equal (fun x => rew [S1] pV1 in Rs zr2 x) kQ)
                  • eq_sym kbQ))))
      • eq_sym kc1)
   ⊙[fun dd => S0 (rf0 dd)]
     (f_equal (fun x => rew [fun dd => S0 (rf0 dd)] e2 in x) kc1
      • (f_equal (fun x => rew [fun dd => S0 (rf0 dd)] e2 in
           rew [S0] gq u1 in Fq (uf0 u1) x) kbQ
         • (rew_cohLayer33 S0 rf0 Fq Fs e2 pV1 pV2 (gq u1) (gs u2) (KA2 zr2)
              (Rs zr2 aQ) (Rq1 zr2 aQ) (HKA2 zr2 aQ) HH2
            • (eq_sym (f_equal (fun x => rew [S0] gs u2 in Fs (uf0 u2) x) kbR)
               • eq_sym kc2)))
      ⊙[fun dd => S0 (rf0 dd)]
        (f_equal (fun x => rew [fun dd => S0 (rf0 dd)] f_equal fB eU2 in x) kc2
         • (sigT_map_eq (P := fun dd => S1 (uf0 dd))
              (Q := fun dd => S0 (rf0 dd)) (f := fB)
              (fun dd x => rew [S0] gs dd in Fs (uf0 dd) x)
              (f_equal (fun x => rew [fun dd => S1 (uf0 dd)] eU2 in x) kbR
               • (f_equal (fun x => rew [fun dd => S1 (uf0 dd)] eU2 in
                    rew [S1] pV2 in Rq1 zr2 x) kQ
                  • (rew_cohLayer33 S1 uf0 Rq1 Rr1 eU2 pIr pIq pV2 pV3 K3
                       (FIr a) (FIq a) HK3 HH3
                     • (eq_sym (f_equal (fun x =>
                          rew [S1] pV3 in Rr1 zq2 x) kR)
                        • eq_sym kbR'))))
            • eq_sym kc3))))
  = f_equal (fun x => rew [fun dd => S0 (rf0 dd)] e4 in x) kc0
    • (f_equal (fun x => rew [fun dd => S0 (rf0 dd)] e4 in
         rew [S0] gq u0 in Fq (uf0 u0) x) kbP
       • (rew_cohLayer33 S0 rf0 Fq Fr e4 pV0 pV4 (gq u0) (gr u4) (KA4 zs2)
            (Rr zs2 aP) (Rq1 zs2 aP) (HKA4 zs2 aP) HH4
          • (eq_sym (f_equal (fun x => rew [S0] gr u4 in Fr (uf0 u4) x) kbW)
             • eq_sym kc4)))
    ⊙[fun dd => S0 (rf0 dd)]
      (f_equal (fun x => rew [fun dd => S0 (rf0 dd)] f_equal fC eU3 in x) kc4
       • (sigT_map_eq (P := fun dd => S1 (uf0 dd))
            (Q := fun dd => S0 (rf0 dd)) (f := fC)
            (fun dd x => rew [S0] gr dd in Fr (uf0 dd) x)
            (f_equal (fun x => rew [fun dd => S1 (uf0 dd)] eU3 in x) kbW
             • (f_equal (fun x => rew [fun dd => S1 (uf0 dd)] eU3 in
                  rew [S1] pV4 in Rq1 zs2 x) kP
                • (rew_cohLayer33 S1 uf0 Rq1 Rs eU3 pIs pIq pV4 pV5 K5
                     (FIs a) (FIq a) HK5 HH5
                   • (eq_sym (f_equal (fun x => rew [S1] pV5 in Rs zq2 x) kR)
                      • eq_sym kbW'))))
          • eq_sym kc5)
       ⊙[fun dd => S0 (rf0 dd)]
         (f_equal (fun x => rew [fun dd => S0 (rf0 dd)] e6 in x) kc5
          • (f_equal (fun x => rew [fun dd => S0 (rf0 dd)] e6 in
               rew [S0] gr u5 in Fr (uf0 u5) x) kbW'
             • (rew_cohLayer33 S0 rf0 Fr Fs e6 pV5 pV3 (gr u5) (gs u3) (KA6 zq2)
                  (Rs zq2 aR) (Rr1 zq2 aR) (HKA6 zq2 aR) HH6
                • (eq_sym (f_equal (fun x =>
                     rew [S0] gs u3 in Fs (uf0 u3) x) kbR')
                   • eq_sym kc3))))).
Proof.
  unfold permutahedral_coherence in Hcoh3Frame.
  subst cA0 cA1 cB2 cB3 cC4 cC5 bP bQ bR bR' bW bW' aP aQ aR.
  cbn [f_equal eq_sym eq_trans].
  destruct pIs, pIr, pIq, eU1, eU2, eU3.
  change (rew [S2] eq_refl in FIs a) with (FIs a).
  change (rew [S2] eq_refl in FIr a) with (FIr a).
  change (rew [S2] eq_refl in FIq a) with (FIq a).
  cbn in HH1, HH3, HH5, κ.
  rewrite 3 sigT_map_eq_refl.
  cbv beta.
  revert K1 K3 K5 pV1 pV3 pV5 pV0 pV2 pV4 HH1 HH3 HH5 HK1 HK3 HK5
    e6 e2 e4 κ HH2 HH4 HH6 HHA Hcoh3Frame Hcoh2Painting.
  generalize (HKA2 zr1 (FIr a)). generalize (HKA4 zs1 (FIs a)).
  generalize (HKA6 zq1 (FIq a)).
  generalize (KA2 zr1). generalize (KA4 zs1). generalize (KA6 zq1).
  generalize (gq u0). generalize (gs u2). generalize (gr u4).
  cbn.
  generalize (Rr zs1 (FIs a)). generalize (Rs zr1 (FIr a)).
  generalize (Rq1 zr1 (FIr a)). generalize (Rr1 zq1 (FIq a)).
  generalize (Rq1 zs1 (FIs a)). generalize (Rs zq1 (FIq a)).
  generalize (fA u0). generalize (fB u2). generalize (fC u4).
  generalize (uf0 u0). generalize (uf0 u2). generalize (uf0 u4).
  generalize (rur zs1). generalize (rus zr1). generalize (ruq1 zr1).
  generalize (rur1 zq1). generalize (ruq1 zs1). generalize (rus zq1).
  intros t t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 s s0 s1 s2 s3 s4 ge gs0 gq0
    k6 k4 k2 hk6 hk4 hk2
    K1 K3 K5 pV1 pV3 pV5 pV0 pV2 pV4 HH1 HH3 HH5 HK1 HK3 HK5
    e6 e2 e4 κ HH2 HH4 HH6 HHA Hcoh3Frame Hcoh2Painting.
  revert ge gs0 gq0 pV0 pV2 pV4 HH1 HH3 HH5 HK1 HK3 HK5 e6 e2 e4
    κ k2 k4 k6 hk2 hk4 hk6 HH2 HH4 HH6 HHA Hcoh3Frame Hcoh2Painting.
  destruct pV1, pV3, pV5.
  intros ge gs0 gq0 pV0 pV2 pV4 HH1 HH3 HH5.
  cbn in HH1, HH3, HH5.
  destruct HH1, HH3, HH5.
  intros HK1 HK3 HK5.
  destruct HK1, HK3, HK5.
  revert ge gs0 gq0.
  destruct pV0, pV2, pV4.
  intros ge gs0 gq0 e6 e2 e4 κ.
  revert e2 e4 κ ge gs0 gq0.
  destruct e6.
  destruct e2.
  intros e4 κ. cbn in κ. destruct κ.
  intros ge gs0 gq0.
  cbn.
  generalize (Fq t4 s4). generalize (Fs t2 s2). generalize (Fr t0 s0).
  revert gq0 gs0 ge.
  generalize (rfq t4). generalize (rfs t2). generalize (rfr t0).
  intros x x0 x1 gq0 gs0 ge p0 p2 p4 k2 k4 k6 hk2 hk4 hk6
    HH2 HH4 HH6 HHA Hcoh3Frame Hcoh2Painting.
  rewrite 3 sigT_trans_eq_refl.
  revert Hcoh2Painting. revert Hcoh3Frame. revert HH2 HH4 HH6. revert HHA.
  revert hk2 hk4 hk6. revert k2 k4 k6. revert p0 p2 p4. revert gs0 ge gq0.
  generalize (rf0 t10).
  destruct gs0.
  destruct ge.
  destruct gq0.
  intros p0 p2 p4 k2 k4 k6 hk2 hk4 hk6 HHA HH2 HH4 HH6 Hcoh3Frame Hcoh2Painting.
  cbn in HH2, HH4, HH6.
  revert hk2 hk4 hk6 HHA Hcoh3Frame Hcoh2Painting.
  destruct HH2, HH4, HH6.
  intros hk2 hk4.
  destruct hk2, hk4.
  intros hk6 HHA Hcoh3Frame Hcoh2Painting.
  cbn in hk6, HHA, Hcoh3Frame, Hcoh2Painting |- *.
  rewrite Hcoh3Frame in Hcoh2Painting.
  cbn in Hcoh2Painting.
  rewrite 2 sigT_trans_eq_refl in Hcoh2Painting.
  change (eq_ind p4 (fun p: S0 x1 => p4 = p) eq_refl p4 hk6)
    with (eq_refl • hk6).
  rewrite 5 eq_trans_refl_l.
  rewrite 2 eq_trans_refl_l in Hcoh2Painting.
  now exact Hcoh2Painting.
Defined.

End Coh2Layer.

Lemma rew_coh2Painting_restr0 {TU TL A0: Type}
  {P: TL -> Type} {S: TU -> Type}
  {rq rr r0: TU -> TL}
  (F: forall m, S m -> P (rq m))
  (G: forall n, S n -> P (rr n))
  {d1 d2: TU} (E1: d1 = d2)
  {m1 m2: TU} (e2: m1 = m2)
  {n1 n2: TU} (e5: n1 = n2)
  (pQ: rq m2 = r0 d1) (pR: rr n2 = r0 d2)
  (KA: rq m1 = rr n1)
  (a0: A0) (AR: A0 -> S m1) (AQ1: A0 -> S n1)
  (HK: rew [P] KA in F m1 (AR a0) = G n1 (AQ1 a0))
  (κ: f_equal rq e2 • (pQ • f_equal r0 E1) = KA • (f_equal rr e5 • pR))
  (u1: S m2) (kF: u1 = rew [S] e2 in AR a0)
  (u12: S n2) (kG: u12 = rew [S] e5 in AQ1 a0)
  (w3: P (r0 d1)) (kM: w3 = rew [P] pQ in F m2 u1)
  (w4: P (r0 d2)) (kM': w4 = rew [P] pR in G n2 u12):
  rew [fun π: rq m1 = r0 d2 => rew [P] π in F m1 (AR a0) = w4] κ in
  (sigT_map_eq (Q := P) F (eq_sym kF)
   ⊙ (eq_sym kM
      ⊙ (eq_sym (rew_map P r0 E1 w3)
         • (f_equal (fun x => rew [fun dd: TU => P (r0 dd)] E1 in x) kM
            • (f_equal (fun x =>
                 rew [fun dd: TU => P (r0 dd)] E1 in rew [P] pQ in F m2 x) kF
               • (rew_cohLayer33 P r0 F G E1 e2 e5 pQ pR KA
                    (AR a0) (AQ1 a0) HK κ
                  • (eq_sym (f_equal (fun x =>
                       rew [P] pR in G n2 x) kG)
                     • eq_sym kM'))))))) =
  HK ⊙ (sigT_map_eq (Q := P) G (eq_sym kG) ⊙ eq_sym kM').
Proof.
  subst u1 u12 w3 w4.
  destruct E1, e2, e5.
  cbn [eq_sym f_equal eq_trans].
  cbn in κ |- *.
  revert κ. revert HK. revert KA. revert pQ. revert pR.
  generalize (r0 d1) as X.
  intros X pR. destruct pR.
  intros pQ KA HK κ.
  cbn in κ.
  revert HK. destruct κ. intros HK.
  cbn in HK |- *.
  destruct HK.
  revert pQ. generalize (rr n1) as Y. intros Y pQ. destruct pQ.
  now reflexivity.
Defined.
