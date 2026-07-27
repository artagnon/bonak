Set Warnings "-notation-overridden".
From Bonak Require Import SigT Notation.

Set Keyed Unification.

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

Lemma rew_cohLayer {T1 T2 T3 X: Type} (P: X -> Type)
  {S2: T2 -> Type} {S3: T3 -> Type}
  (rf0: T1 -> X) {rfF: T2 -> X} {rfG: T3 -> X}
  (F: forall m, S2 m -> P (rfF m))
  (G: forall n, S3 n -> P (rfG n))
  {d1 d2: T1} (E1: d1 = d2)
  {m1 m2: T2} (C2: m1 = m2)
  {n1 n2: T3} (D2: n1 = n2)
  (C1: rfF m2 = rf0 d1) (D1: rfG n2 = rf0 d2)
  (K: rfF m1 = rfG n1)
  (aL: S2 m1) (aR: S3 n1):
  rew [P] K in F m1 aL = G n1 aR ->
  f_equal rfF C2 • (C1 • f_equal rf0 E1) =
  K • (f_equal rfG D2 • D1) ->
  rew [fun d => P (rf0 d)] E1 in rew [P] C1 in F m2 (rew [S2] C2 in aL)
  = rew [P] D1 in G n2 (rew [S3] D2 in aR).
Proof.
  intros HC Hpath.
  rewrite <- (map_subst F C2 aL), <- (map_subst G D2 aR).
  rewrite <- HC.
  rewrite (rew_map P rf0 E1), (rew_map P rfF C2), (rew_map P rfG D2).
  rewrite 4 rew_compose.
  now exact (f_equal (fun h => rew [P] h in F m1 aL) Hpath).
Defined.

Lemma rew_coh2Painting_restr0 {Tp Td: Type} {S: Tp -> Type} (P: Td -> Type)
  (rf0: Tp -> Td) {rfF rfG: Tp -> Td}
  (F: forall m, S m -> P (rfF m))
  (G: forall n, S n -> P (rfG n))
  {d1 d2: Tp} (E1: d1 = d2)
  {m1 m2: Tp} (C2: m1 = m2)
  {n1 n2: Tp} (D2: n1 = n2)
  (C1: rfF m2 = rf0 d1) (D1: rfG n2 = rf0 d2)
  (K: rfF m1 = rfG n1)
  (aL: S m1) (aR: S n1)
  (HK: rew [P] K in F m1 aL = G n1 aR)
  (HH: f_equal rfF C2 • (C1 • f_equal rf0 E1) =
       K • (f_equal rfG D2 • D1))
  (R0: {a: Tp &T P (rf0 a)} -> Type)
  {v0: R0 (d1; rew [P] C1 in F m2 (rew [S] C2 in aL))}
  {v1: R0 (d2; rew [P] D1 in G n2 (rew [S] D2 in aR))}
  (Hv: rew [R0] (= E1; rew_cohLayer P rf0 F G E1 C2 D2 C1 D1 K aL aR HK HH)
    in v0 = v1):
  rew [fun π: rfF m1 = rf0 d2 =>
      rew [P] π in F m1 aL = rew [P] D1 in G n2 (rew [S] D2 in aR)] HH in
  (sigT_map_eq (Q := P) F (eq_refl (x := rew [S] C2 in aL))
   ⊙ ((eq_refl : rew [P] C1 in F m2 (rew [S] C2 in aL)
       = rew [P] C1 in F m2 (rew [S] C2 in aL))
      ⊙ sigT_map_eq (P := fun a => {u: P (rf0 a) &T R0 (a; u)}) (Q := P)
          (f := rf0) (fun a uv => uv.1)
          (eq_existT_curried_dep (Q := R0) (H := E1)
            (Hu := rew_cohLayer P rf0 F G E1 C2 D2 C1 D1 K aL aR HK HH)
            (Hv := Hv)))) =
  HK ⊙ (sigT_map_eq (Q := P) G (eq_refl (x := rew [S] D2 in aR)) ⊙ eq_refl).
Proof.
  rewrite (sigT_map_eq_existT_curried_dep_fst rf0 (fun a u => u) E1
    (rew_cohLayer P rf0 F G E1 C2 D2 C1 D1 K aL aR HK HH) Hv).
  cbn [projT1].
  clear Hv v0 v1 R0.
  destruct E1, C2, D2.
  cbn in HH |- *.
  revert HH. revert HK. revert C1. revert D1.
  generalize (G n1 aR) as gb.
  intros gb D1 C1 HK HH.
  rewrite (sigT_map_eq_id_refl rf0).
  revert HH. revert HK. revert C1. revert D1.
  generalize (rf0 d1) as X.
  intros X D1.
  destruct D1.
  intros C1 HK HH.
  cbn in HH.
  revert HK.
  destruct HH.
  intros HK.
  cbn in HK |- *.
  destruct HK.
  revert C1.
  generalize (rfG n1) as Y.
  intros Y C1.
  destruct C1.
  now reflexivity.
Defined.

Section Coh2Layer.

Variables (T1 T0 XA: Type).
Variable S1: T1 -> Type.
Variable S0: T0 -> Type.
Variable PA: XA -> Type.

Variables (g0 uq1 ur ur1 us hq hr hs: T1 -> T0).
Variables (f0 fq fr fs: T0 -> XA).

Variable Rr: forall x, S1 x -> S0 (ur x).
Variable Rs: forall x, S1 x -> S0 (us x).
Variable Rq1: forall x, S1 x -> S0 (uq1 x).
Variable Rr1: forall x, S1 x -> S0 (ur1 x).
Variable Fq: forall y, S0 y -> PA (fq y).
Variable Fr: forall y, S0 y -> PA (fr y).
Variable Fs: forall y, S0 y -> PA (fs y).

Variable gq: forall x, fq (g0 x) = f0 (hq x).
Variable gr: forall x, fr (g0 x) = f0 (hr x).
Variable gs: forall x, fs (g0 x) = f0 (hs x).

Variable KA2: forall x, fq (us x) = fs (uq1 x).
Variable KA4: forall x, fq (ur x) = fr (uq1 x).
Variable KA6: forall x, fr (us x) = fs (ur1 x).

Variable HKA2: forall x (c: S1 x),
  rew [PA] KA2 x in Fq (us x) (Rs x c) = Fs (uq1 x) (Rq1 x c).
Variable HKA4: forall x (c: S1 x),
  rew [PA] KA4 x in Fq (ur x) (Rr x c) = Fr (uq1 x) (Rq1 x c).
Variable HKA6: forall x (c: S1 x),
  rew [PA] KA6 x in Fr (us x) (Rs x c) = Fs (ur1 x) (Rr1 x c).

(** The permutahedral coherence of frames: the hexagon proved as a
    composition of the seven other hexagons of the permutahedron. The six
    squares hold by naturality and don't appear here explicitly. *)
Lemma permutahedral_coherence
  (n1 n2 n3 m1 m2 m3 dd11 dd21 dd13 dd23 dd15 dd25: T1)
  (b1: n1 = m1) (b2: n2 = m2) (b3: n3 = m3)
  (KB1: ur n1 = us n2) (KB3: uq1 n2 = ur1 n3) (KB5: uq1 n1 = us n3)
  (E11: dd11 = dd21) (E13: dd13 = dd23) (E15: dd15 = dd25)
  (C11: ur m1 = g0 dd11) (D11: us m2 = g0 dd21)
  (C13: uq1 m2 = g0 dd13) (D13: ur1 m3 = g0 dd23)
  (C15: uq1 m1 = g0 dd15) (D15: us m3 = g0 dd25)
  (E12: hq dd21 = hs dd13) (E14: hq dd11 = hr dd15)
  (E16: hr dd25 = hs dd23)
  (HHB1: f_equal ur b1 • (C11 • f_equal g0 E11) =
         KB1 • (f_equal us b2 • D11))
  (HHB3: f_equal uq1 b2 • (C13 • f_equal g0 E13) =
         KB3 • (f_equal ur1 b3 • D13))
  (HHB5: f_equal uq1 b1 • (C15 • f_equal g0 E15) =
         KB5 • (f_equal us b3 • D15))
  (HH2: f_equal fq D11 • (gq dd21 • f_equal f0 E12) =
        KA2 m2 • (f_equal fs C13 • gs dd13))
  (HH4: f_equal fq C11 • (gq dd11 • f_equal f0 E14) =
        KA4 m1 • (f_equal fr C15 • gr dd15))
  (HH6: f_equal fr D15 • (gr dd25 • f_equal f0 E16) =
        KA6 m3 • (f_equal fs D13 • gs dd23))
  (HHs: f_equal hq E11 • (E12 • f_equal hs E13) =
        E14 • (f_equal hr E15 • E16)):
  f_equal fq KB1 • (KA2 n2 • f_equal fs KB3) =
  KA4 n1 • (f_equal fr KB5 • KA6 n3).
Proof.
  destruct b1, b2, b3, E11, E13, E15.
  cbn in HHB1, HHB3, HHB5, HHs.
  revert KB1 KB3 KB5 D11 D13 D15 C11 C13 C15 HHB1 HHB3 HHB5
    E16 E12 E14 HHs HH2 HH4 HH6.
  generalize (KA2 n2). generalize (KA4 n1). generalize (KA6 n3).
  generalize (gq dd11). generalize (gs dd13). generalize (gr dd15).
  generalize (hq dd11). generalize (hs dd13). generalize (hr dd15).
  generalize (g0 dd11). generalize (g0 dd13). generalize (g0 dd15).
  generalize (ur n1). generalize (us n2). generalize (uq1 n2).
  generalize (ur1 n3). generalize (uq1 n1). generalize (us n3).
  intros t t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 ge gs0 gq0 k6 k4 k2
    KB1 KB3 KB5 D11 D13 D15 C11 C13 C15 HHB1 HHB3 HHB5
    E16 E12 E14 HHs HH2 HH4 HH6.
  revert ge gs0 gq0 C11 C13 C15 HHB1 HHB3 HHB5 E16 E12 E14 HHs HH2 HH4 HH6.
  destruct D11, D13, D15.
  intros ge gs0 gq0 C11 C13 C15 HHB1 HHB3 HHB5.
  cbn in HHB1, HHB3, HHB5.
  destruct HHB1, HHB3, HHB5.
  revert ge gs0 gq0.
  destruct C11, C13, C15.
  intros ge gs0 gq0 E16 E12 E14 HHs.
  revert E12 E14 HHs ge gs0 gq0.
  destruct E16.
  destruct E12.
  intros E14 HHs. cbn in HHs. destruct HHs.
  intros ge gs0 gq0.
  revert k2 k4 k6.
  revert gs0 ge gq0.
  cbn.
  generalize (fq t4). generalize (fs t2). generalize (fr t0).
  generalize (f0 t10).
  destruct gs0.
  destruct ge.
  destruct gq0.
  intros k2 k4 k6 HH2 HH4 HH6.
  cbn in HH2, HH4, HH6.
  destruct HH2, HH4, HH6.
  now reflexivity.
Defined.

Lemma rew_coh2Layer
  (n1 n2 n3 m1 m2 m3 dd11 dd21 dd13 dd23 dd15 dd25: T1)
  (a1: S1 n1) (a2: S1 n2) (a3: S1 n3)
  (b1: n1 = m1) (b2: n2 = m2) (b3: n3 = m3)
  (KB1: ur n1 = us n2) (KB3: uq1 n2 = ur1 n3) (KB5: uq1 n1 = us n3)
  (E11: dd11 = dd21) (E13: dd13 = dd23) (E15: dd15 = dd25)
  (C11: ur m1 = g0 dd11) (D11: us m2 = g0 dd21)
  (C13: uq1 m2 = g0 dd13) (D13: ur1 m3 = g0 dd23)
  (C15: uq1 m1 = g0 dd15) (D15: us m3 = g0 dd25)
  (E12: hq dd21 = hs dd13) (E14: hq dd11 = hr dd15)
  (E16: hr dd25 = hs dd23)
  (HKB1: rew [S0] KB1 in Rr n1 a1 = Rs n2 a2)
  (HKB3: rew [S0] KB3 in Rq1 n2 a2 = Rr1 n3 a3)
  (HKB5: rew [S0] KB5 in Rq1 n1 a1 = Rs n3 a3)
  (HHB1: f_equal ur b1 • (C11 • f_equal g0 E11) =
         KB1 • (f_equal us b2 • D11))
  (HHB3: f_equal uq1 b2 • (C13 • f_equal g0 E13) =
         KB3 • (f_equal ur1 b3 • D13))
  (HHB5: f_equal uq1 b1 • (C15 • f_equal g0 E15) =
         KB5 • (f_equal us b3 • D15))
  (HH2: f_equal fq D11 • (gq dd21 • f_equal f0 E12) =
        KA2 m2 • (f_equal fs C13 • gs dd13))
  (HH4: f_equal fq C11 • (gq dd11 • f_equal f0 E14) =
        KA4 m1 • (f_equal fr C15 • gr dd15))
  (HH6: f_equal fr D15 • (gr dd25 • f_equal f0 E16) =
        KA6 m3 • (f_equal fs D13 • gs dd23))
  (HHA: f_equal fq KB1 • (KA2 n2 • f_equal fs KB3) =
        KA4 n1 • (f_equal fr KB5 • KA6 n3))
  (HHs: f_equal hq E11 • (E12 • f_equal hs E13) =
        E14 • (f_equal hr E15 • E16))
  (Hcoh2Painting:
    rew [fun pi: fq (ur n1) = fs (ur1 n3) =>
        rew [PA] pi in Fq (ur n1) (Rr n1 a1) = Fs (ur1 n3) (Rr1 n3 a3)]
      HHA in
    (sigT_map_eq Fq HKB1 ⊙ (HKA2 n2 a2 ⊙ sigT_map_eq Fs HKB3)) =
    HKA4 n1 a1 ⊙ (sigT_map_eq Fr HKB5 ⊙ HKA6 n3 a3))
  (Hcoh3Frame: HHA =
    permutahedral_coherence n1 n2 n3 m1 m2 m3 dd11 dd21 dd13 dd23 dd15 dd25
      b1 b2 b3 KB1 KB3 KB5 E11 E13 E15 C11 D11 C13 D13 C15 D15 E12 E14 E16
      HHB1 HHB3 HHB5 HH2 HH4 HH6 HHs):
  rew [fun pi: hq dd11 = hs dd23 =>
      rew [fun y => PA (f0 y)] pi in
      rew [PA] gq dd11 in
        Fq (g0 dd11) (rew [S0] C11 in Rr m1 (rew [S1] b1 in a1)) =
      rew [PA] gs dd23 in
        Fs (g0 dd23) (rew [S0] D13 in Rr1 m3 (rew [S1] b3 in a3))]
    HHs in
  (sigT_map_eq (fun x v => rew [PA] gq x in Fq (g0 x) v)
     (rew_cohLayer S0 g0 Rr Rs E11 b1 b2 C11 D11 KB1 a1 a2 HKB1 HHB1)
   ⊙ (rew_cohLayer PA f0 Fq Fs E12 D11 C13 (gq dd21) (gs dd13) (KA2 m2)
        (Rs m2 (rew [S1] b2 in a2)) (Rq1 m2 (rew [S1] b2 in a2))
        (HKA2 m2 (rew [S1] b2 in a2)) HH2
      ⊙ sigT_map_eq (fun x v => rew [PA] gs x in Fs (g0 x) v)
          (rew_cohLayer S0 g0 Rq1 Rr1 E13 b2 b3 C13 D13 KB3 a2 a3
             HKB3 HHB3))) =
  rew_cohLayer PA f0 Fq Fr E14 C11 C15 (gq dd11) (gr dd15) (KA4 m1)
    (Rr m1 (rew [S1] b1 in a1)) (Rq1 m1 (rew [S1] b1 in a1))
    (HKA4 m1 (rew [S1] b1 in a1)) HH4
  ⊙ (sigT_map_eq (fun x v => rew [PA] gr x in Fr (g0 x) v)
       (rew_cohLayer S0 g0 Rq1 Rs E15 b1 b3 C15 D15 KB5 a1 a3 HKB5 HHB5)
     ⊙ rew_cohLayer PA f0 Fr Fs E16 D15 D13 (gr dd25) (gs dd23) (KA6 m3)
         (Rs m3 (rew [S1] b3 in a3)) (Rr1 m3 (rew [S1] b3 in a3))
         (HKA6 m3 (rew [S1] b3 in a3)) HH6).
Proof.
  unfold permutahedral_coherence in Hcoh3Frame.
  destruct b1, b2, b3, E11, E13, E15.
  lazy beta iota delta [f_equal].
  change (rew [S1] eq_refl in a1) with a1.
  change (rew [S1] eq_refl in a2) with a2.
  change (rew [S1] eq_refl in a3) with a3.
  cbn in HHB1, HHB3, HHB5, HHs.
  revert KB1 KB3 KB5 C11 D11 C13 D13 C15 D15 E12 E14 E16 HKB1 HKB3 HKB5
    HHB1 HHB3 HHB5 HH2 HH4 HH6 HHA HHs Hcoh3Frame Hcoh2Painting.
  generalize (HKA2 n2 a2). generalize (HKA4 n1 a1). generalize (HKA6 n3 a3).
  generalize (KA2 n2). generalize (KA4 n1). generalize (KA6 n3).
  intros k6 k4 k2 hk6 hk4 hk2 KB1 KB3 KB5 C11 D11 C13 D13 C15 D15
    E12 E14 E16 HKB1 HKB3 HKB5 HHB1 HHB3 HHB5 HH2 HH4 HH6 HHA HHs
    Hcoh3Frame Hcoh2Painting.
  rewrite 3 sigT_map_eq_refl.
  cbv beta.
  revert KB1 KB3 KB5 D11 D13 D15 C11 C13 C15 HHB1 HHB3 HHB5 HKB1 HKB3 HKB5
    E16 E12 E14 HHs k2 k4 k6 hk2 hk4 hk6 HH2 HH4 HH6 HHA Hcoh3Frame Hcoh2Painting.
  generalize (gq dd11). generalize (gs dd13). generalize (gr dd15).
  cbn.
  generalize (Rr n1 a1). generalize (Rs n2 a2). generalize (Rq1 n2 a2).
  generalize (Rr1 n3 a3). generalize (Rq1 n1 a1). generalize (Rs n3 a3).
  generalize (hq dd11). generalize (hs dd13). generalize (hr dd15).
  generalize (g0 dd11). generalize (g0 dd13). generalize (g0 dd15).
  generalize (ur n1). generalize (us n2). generalize (uq1 n2).
  generalize (ur1 n3). generalize (uq1 n1). generalize (us n3).
  intros t t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 s s0 s1 s2 s3 s4 ge gs0 gq0
    KB1 KB3 KB5 D11 D13 D15 C11 C13 C15 HHB1 HHB3 HHB5 HKB1 HKB3 HKB5
    E16 E12 E14 HHs k2 k4 k6 hk2 hk4 hk6 HH2 HH4 HH6 HHA Hcoh3Frame Hcoh2Painting.
  revert ge gs0 gq0 C11 C13 C15 HHB1 HHB3 HHB5 HKB1 HKB3 HKB5 E16 E12 E14
    HHs k2 k4 k6 hk2 hk4 hk6 HH2 HH4 HH6 HHA Hcoh3Frame Hcoh2Painting.
  destruct D11, D13, D15.
  intros ge gs0 gq0 C11 C13 C15 HHB1 HHB3 HHB5.
  cbn in HHB1, HHB3, HHB5.
  destruct HHB1, HHB3, HHB5.
  intros HKB1 HKB3 HKB5.
  destruct HKB1, HKB3, HKB5.
  revert ge gs0 gq0.
  destruct C11, C13, C15.
  intros ge gs0 gq0 E16 E12 E14 HHs.
  revert E12 E14 HHs ge gs0 gq0.
  destruct E16.
  destruct E12.
  intros E14 HHs. cbn in HHs. destruct HHs.
  intros ge gs0 gq0.
  cbn.
  generalize (Fq t4 s4). generalize (Fs t2 s2). generalize (Fr t0 s0).
  revert gq0 gs0 ge.
  generalize (fq t4). generalize (fs t2). generalize (fr t0).
  intros x x0 x1 gq0 gs0 ge p0 p2 p4 k2 k4 k6 hk2 hk4 hk6
    HH2 HH4 HH6 HHA Hcoh3Frame Hcoh2Painting.
  rewrite 3 sigT_trans_eq_refl.
  revert Hcoh2Painting. revert Hcoh3Frame. revert HH2 HH4 HH6. revert HHA.
  revert hk2 hk4 hk6. revert k2 k4 k6. revert p0 p2 p4. revert gs0 ge gq0.
  generalize (f0 t10).
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
  change (eq_ind p4 (fun p: PA x1 => p4 = p) eq_refl p4 hk6) with (eq_refl • hk6).
  rewrite eq_trans_refl_l.
  now exact Hcoh2Painting.
Defined.

End Coh2Layer.
