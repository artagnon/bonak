(** A few rewriting lemmas not in the standard library *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation.

Lemma rew_permute_ll_hset: forall (A: Type) (P Q: A -> HSet) (x y: A)
  (H: forall z: A, P z = Q z) (H': x = y) (a: P x),
  rew [Dom] H y in rew [P] H' in a = rew [Q] H' in rew [Dom] H x in a.
Proof.
  now destruct H'.
Defined.

Lemma rew_swap: forall A (P: A -> Type) a b (H: a = b) (x: P a) (y: P b),
  x = rew <- H in y <-> rew H in x = y.
Proof.
  now destruct H.
Qed.

Lemma rew_app_rl A (P: A -> Type) (x y: A) (H H': x = y) (a: P x) :
  H = H' -> rew <- [P] H in rew [P] H' in a = a.
Proof.
  intros * ->. now destruct H'.
Qed.

Lemma map_subst_app {A B} {x y} {𝛉: A} (H: x = y :> B) (P: A -> B -> Type)
  (f: forall 𝛉, P 𝛉 x):
  rew [P 𝛉] H in f 𝛉 = (rew [fun x => forall 𝛉, P 𝛉 x] H in f) 𝛉.
Proof.
  now destruct H.
Qed.

(** Fused transport-chain lemmas.

    Each lemma equates, in one step, two forward chains of transports of the
    same element — the goal shape of the layer coherence proofs after
    [map_subst]. The digits name the number of transports on each side of
    the equation. The premises are an equation between the transported
    elements ([reflexivity] at the use sites) and an equation between the two
    composite paths: the higher coherence, which every caller exhibits
    explicitly — [UIP] in an HSet development. *)

Lemma rew_chain13 {X B1 B2: Type} (P: X -> Type)
  (f: B1 -> X) (g: B2 -> X)
  {u1 v1: B1} {u3 v3: B2}
  (E1: u1 = v1)
  (F1: g v3 = f v1) (F2: u3 = v3) (F3: f u1 = g u3)
  (aL aR: P (f u1)):
  aL = aR ->
  f_equal f E1 = F3 • (f_equal g F2 • F1) ->
  rew [fun x => P (f x)] E1 in aL
  = rew [P] F1 in rew [fun x => P (g x)] F2 in rew [P] F3 in aR.
Proof.
  intros base coh2. destruct base, E1, F2. cbn in coh2 |- *.
  rewrite rew_compose.
  rewrite eq_trans_refl_l in coh2.
  now rewrite <- coh2.
Qed.

Lemma rew_chain31 {X B1 B2: Type} (P: X -> Type)
  (f1: B1 -> X) (f2: B2 -> X)
  {u1 v1: B1} {u2 v2: B2}
  (E1: u1 = v1) (E2: f2 v2 = f1 u1) (E3: u2 = v2)
  (F1: f2 u2 = f1 v1)
  (aL aR: P (f2 u2)):
  aL = aR ->
  f_equal f2 E3 • (E2 • f_equal f1 E1) = F1 ->
  rew [fun x => P (f1 x)] E1 in rew [P] E2 in rew [fun x => P (f2 x)] E3 in aL
  = rew [P] F1 in aR.
Proof.
  intros base coh2. destruct base, E1, E3. cbn in coh2 |- *.
  rewrite eq_trans_refl_l in coh2.
  now rewrite coh2.
Qed.

Lemma rew_chain22 {X B1 B2: Type} (P: X -> Type)
  (f: B1 -> X) (g: B2 -> X)
  {u v: B1} {w w': B2}
  (E1: u = v) (E0: g w = f u)
  (F1: g w' = f v) (F2: w = w')
  (aL aR: P (g w)):
  aL = aR ->
  E0 • f_equal f E1 = f_equal g F2 • F1 ->
  rew [fun x => P (f x)] E1 in rew [P] E0 in aL
  = rew [P] F1 in rew [fun x => P (g x)] F2 in aR.
Proof.
  intros base coh2. destruct base, E1, F2. cbn in coh2 |- *.
  rewrite eq_trans_refl_l in coh2.
  now rewrite coh2.
Qed.

Lemma rew_chain33 {X B1 B2 B3: Type} (P: X -> Type)
  (f1: B1 -> X) (f2: B2 -> X) (g: B3 -> X)
  {u1 v1: B1} {u2 v2: B2} {u3 v3: B3}
  (E1: u1 = v1) (E2: f2 v2 = f1 u1) (E3: u2 = v2)
  (F1: g v3 = f1 v1) (F2: u3 = v3) (F3: f2 u2 = g u3)
  (aL aR: P (f2 u2)):
  aL = aR ->
  f_equal f2 E3 • (E2 • f_equal f1 E1) = F3 • (f_equal g F2 • F1) ->
  rew [fun x => P (f1 x)] E1 in rew [P] E2 in rew [fun x => P (f2 x)] E3 in aL
  = rew [P] F1 in rew [fun x => P (g x)] F2 in rew [P] F3 in aR.
Proof.
  intros base coh2. destruct base, E1, E3, F2. cbn in coh2 |- *.
  rewrite rew_compose.
  rewrite !eq_trans_refl_l in coh2.
  now rewrite coh2.
Qed.

(** Fused layer-chain lemmas.

    On top of [rew_chain*] lemmas above, they additionally absorb the head of the layer
    coherence proofs — the commutation of the pointwise ([map_subst_app]) and
    fiberwise ([map_subst]) transports — so that a layer coherence proof
    reduces to [functional_extensionality_dep] followed by a single
    application. *)

Lemma rew_layer13 {A T1 T3 X: Type} {P: X -> Type} {S3: T3 -> Type}
  {rf0: A -> T1 -> X} {rfG: T3 -> X}
  {G: forall n, S3 n -> P (rfG n)}
  {𝛉: A}
  {d1 d2: T1} {E1: d1 = d2}
  {n1 n2: T3} {D2: n1 = n2}
  {D1: rfG n2 = rf0 𝛉 d2}
  {K: rf0 𝛉 d1 = rfG n1}
  {aL: P (rf0 𝛉 d1)} {aR: S3 n1}
  {L: forall a, P (rf0 a d1)}:
  L 𝛉 = aL ->
  rew [P] K in aL = G n1 aR ->
  f_equal (rf0 𝛉) E1 = K • (f_equal rfG D2 • D1) ->
  (rew [fun d => forall a, P (rf0 a d)] E1 in L) 𝛉
  = rew [P] D1 in G n2 (rew [S3] D2 in aR).
Proof.
  intros HL HC Hpath.
  rewrite <- (map_subst_app E1 (fun a d => P (rf0 a d)) L), HL,
    <- (map_subst G D2 aR), <- HC.
  exact (rew_chain13 P (rf0 𝛉) rfG E1 D1 D2 K aL aL eq_refl Hpath).
Qed.

Lemma rew_layer22 {A T1 T3 X: Type} {P: X -> Type} {S3: T3 -> Type}
  {rf0: A -> T1 -> X} {rfG: T3 -> X}
  {G: forall n, S3 n -> P (rfG n)}
  {𝛉: A}
  {d1 d2: T1} {E1: d1 = d2}
  {n1 n2: T3} {D2: n1 = n2}
  {E0: rfG n1 = rf0 𝛉 d1}
  {D1: rfG n2 = rf0 𝛉 d2}
  {aL: P (rfG n1)} {aR: S3 n1}
  {L: forall a, P (rf0 a d1)}:
  L 𝛉 = rew [P] E0 in aL ->
  aL = G n1 aR ->
  E0 • f_equal (rf0 𝛉) E1 = f_equal rfG D2 • D1 ->
  (rew [fun d => forall a, P (rf0 a d)] E1 in L) 𝛉
  = rew [P] D1 in G n2 (rew [S3] D2 in aR).
Proof.
  intros HL HC Hpath.
  rewrite <- (map_subst_app E1 (fun a d => P (rf0 a d)) L), HL,
    <- (map_subst G D2 aR), <- HC.
  exact (rew_chain22 P (rf0 𝛉) rfG E1 E0 D1 D2 aL aL eq_refl Hpath).
Qed.

Lemma rew_layer31 {A T1 T2 X: Type} {P: X -> Type} {S2: T2 -> Type}
  {rf0: A -> T1 -> X} {rfF: T2 -> X}
  {F: forall m, S2 m -> P (rfF m)}
  {𝛉: A}
  {d1 d2: T1} {E1: d1 = d2}
  {m1 m2: T2} {C2: m1 = m2}
  {C1: rfF m2 = rf0 𝛉 d1}
  {D1: rfF m1 = rf0 𝛉 d2}
  {aL: S2 m1} {aR: P (rfF m1)}
  {L: forall a, P (rf0 a d1)}:
  L 𝛉 = rew [P] C1 in F m2 (rew [S2] C2 in aL) ->
  F m1 aL = aR ->
  f_equal rfF C2 • (C1 • f_equal (rf0 𝛉) E1) = D1 ->
  (rew [fun d => forall a, P (rf0 a d)] E1 in L) 𝛉
  = rew [P] D1 in aR.
Proof.
  intros HL HC Hpath.
  rewrite <- (map_subst_app E1 (fun a d => P (rf0 a d)) L), HL,
    <- (map_subst F C2 aL).
  exact (rew_chain31 P (rf0 𝛉) rfF E1 C1 C2 D1 (F m1 aL) aR HC Hpath).
Qed.

Lemma rew_layer33 {A T1 T2 T3 X: Type} {P: X -> Type}
  {S2: T2 -> Type} {S3: T3 -> Type}
  {rf0: A -> T1 -> X} {rfF: T2 -> X} {rfG: T3 -> X}
  {F: forall m, S2 m -> P (rfF m)}
  {G: forall n, S3 n -> P (rfG n)}
  {𝛉: A}
  {d1 d2: T1} {E1: d1 = d2}
  {m1 m2: T2} {C2: m1 = m2}
  {n1 n2: T3} {D2: n1 = n2}
  {C1: rfF m2 = rf0 𝛉 d1}
  {D1: rfG n2 = rf0 𝛉 d2}
  {K: rfF m1 = rfG n1}
  {aL: S2 m1} {aR: S3 n1}
  {L: forall a, P (rf0 a d1)}:
  L 𝛉 = rew [P] C1 in F m2 (rew [S2] C2 in aL) -> (* reflexivity *)
  rew [P] K in F m1 aL = G n1 aR -> (* painting coherence *)
  f_equal rfF C2 • (C1 • f_equal (rf0 𝛉) E1) = K • (f_equal rfG D2 • D1) ->
  (* 2-dimensional frame coherence, UIP for HSets *)
  (rew [fun d => forall a, P (rf0 a d)] E1 in L) 𝛉
  = rew [P] D1 in G n2 (rew [S3] D2 in aR).
Proof.
  intros HL HC Hpath.
  rewrite <- (map_subst_app E1 (fun a d => P (rf0 a d)) L), HL,
    <- (map_subst F C2 aL), <- (map_subst G D2 aR), <- HC.
  exact (rew_chain33 P (rf0 𝛉) rfF rfG E1 C1 C2 D1 D2 K (F m1 aL) (F m1 aL)
    eq_refl Hpath).
Qed.
