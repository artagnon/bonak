(** A few rewriting lemmas not in the standard library *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation Chain.

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
Defined.

Lemma rew_app_rl A (P: A -> Type) (x y: A) (H H': x = y) (a: P x):
  H = H' -> rew <- [P] H in rew [P] H' in a = a.
Proof.
  intros * ->. now destruct H'.
Defined.

Lemma map_subst_app {A B} {x y} {θ: A} (H: x = y :> B) (P: A -> B -> Type)
  (f: forall θ, P θ x):
  rew [P θ] H in f θ = (rew [fun x => forall θ, P θ x] H in f) θ.
Proof.
  now destruct H.
Defined.

Lemma f_equal_id {A} {x y: A} (e: x = y): f_equal (fun x => x) e = e.
Proof.
  now destruct e.
Defined.

Lemma eq_trans_sym_cancel_l {A: Type} {x y z: A} (e: x = y) (h: y = z):
  eq_sym e • (e • h) = h.
Proof.
  now destruct e, h.
Defined.

(** Fused transport-chain lemmas for layer coherence proofs

    The [rew_cohLayer] lemma closes a layer coherence goal in one step, once a
    bridge (Layer.v) has taken the pointwise step: it equates two chains of
    transports, whose starting elements are identified by the painting
    coherence. A call site supplies only the two premises: the painting
    coherence and the 2-dimensional frame coherence ([UIP] in HSet development).

    The [rew_cohLayer<NM>] lemmas are a family of specialized versions for
    different coherence shapes, in which every side is a single arrow or
    trivial. N and M count the arrows on each side of the frame coherence. *)

Lemma rew_cohLayer {T1 T2 T3 X: Type} {P: X -> Type}
  {S2: T2 -> Type} {S3: T3 -> Type}
  {rf0: T1 -> X} {rfF: T2 -> X} {rfG: T3 -> X}
  {F: forall m, S2 m -> P (rfF m)}
  {G: forall n, S3 n -> P (rfG n)}
  {d1 d2: T1} {E1: d1 = d2}
  {m1 m2: T2} {C2C: Chain m1 m2}
  {n1 n2: T3} {D2C: Chain n1 n2}
  {C1C: Chain (rfF m2) (rf0 d1)}
  {D1: rfG n2 = rf0 d2}
  {KC: Chain (rfF m1) (rfG n1)}
  {aL: S2 m1} {aR: S3 n1}:
  (* painting coherence: *)
  rew [P] ⟦KC⟧ in F m1 aL = G n1 aR ->
  (* 2-dimensional frame coherence, [UIP] for HSets: *)
  ⟦capp (cmap rfF C2C) (capp C1C [: f_equal rf0 E1 :])⟧
  = ⟦capp KC (capp (cmap rfG D2C) [: D1 :])⟧ ->
  rew [fun d => P (rf0 d)] E1 in rew [P] ⟦C1C⟧ in F m2 (rew [S2] ⟦C2C⟧ in aL)
  = rew [P] D1 in G n2 (rew [S3] ⟦D2C⟧ in aR).
Proof.
  intros HC Hpath.
  rewrite 4 interp_capp, 2 interp_cmap in Hpath.
  revert HC Hpath.
  generalize ⟦KC⟧ as K; generalize ⟦C1C⟧ as C1.
  generalize ⟦D2C⟧ as D2; generalize ⟦C2C⟧ as C2.
  intros C2 D2 C1 K HC Hpath.
  rewrite <- (map_subst F C2 aL), <- (map_subst G D2 aR), <- HC.
  destruct E1, C2, D2.
  cbn in Hpath |- *.
  rewrite rew_compose.
  rewrite 2 eq_trans_refl_l in Hpath.
  now rewrite Hpath.
Defined.

Lemma rew_cohLayer33 {T1 T2 T3 X: Type} {P: X -> Type}
  {S2: T2 -> Type} {S3: T3 -> Type}
  {rf0: T1 -> X} {rfF: T2 -> X} {rfG: T3 -> X}
  {F: forall m, S2 m -> P (rfF m)}
  {G: forall n, S3 n -> P (rfG n)}
  {d1 d2: T1} {E1: d1 = d2}
  {m1 m2: T2} {C2: m1 = m2}
  {n1 n2: T3} {D2: n1 = n2}
  {C1: rfF m2 = rf0 d1}
  {D1: rfG n2 = rf0 d2}
  {K: rfF m1 = rfG n1}
  {aL: S2 m1} {aR: S3 n1}:
  (* painting coherence: *)
  rew [P] K in F m1 aL = G n1 aR ->
  (* 2-dimensional frame coherence, [UIP] for HSets: *)
  f_equal rfF C2 • (C1 • f_equal rf0 E1) = K • (f_equal rfG D2 • D1) ->
  rew [fun d => P (rf0 d)] E1 in rew [P] C1 in F m2 (rew [S2] C2 in aL)
  = rew [P] D1 in G n2 (rew [S3] D2 in aR).
Proof.
  now exact (rew_cohLayer (P := P) (S2 := S2) (S3 := S3) (rf0 := rf0)
    (rfF := rfF) (rfG := rfG) (F := F) (G := G)
    (C2C := [: C2 :]) (D2C := [: D2 :]) (KC := [: K :]) (C1C := [: C1 :])).
Defined.

Lemma rew_cohLayer13 {T1 T3 X: Type} {P: X -> Type} {S3: T3 -> Type}
  {rf0: T1 -> X} {rfG: T3 -> X}
  {G: forall n, S3 n -> P (rfG n)}
  {d1 d2: T1} {E1: d1 = d2}
  {n1 n2: T3} {D2: n1 = n2}
  {D1: rfG n2 = rf0 d2}
  {K: rf0 d1 = rfG n1}
  {aL: P (rf0 d1)} {aR: S3 n1}:
  rew [P] K in aL = G n1 aR ->
  f_equal rf0 E1 = K • (f_equal rfG D2 • D1) ->
  rew [fun d => P (rf0 d)] E1 in aL
  = rew [P] D1 in G n2 (rew [S3] D2 in aR).
Proof.
  now exact (rew_cohLayer (P := P) (S2 := P) (rf0 := rf0)
    (rfF := fun x => x) (F := fun _ a => a)
    (C2C := cnil) (D2C := [: D2 :]) (KC := [: K :]) (C1C := cnil)
    (aL := aL)).
Defined.

Lemma rew_cohLayer22 {T1 T3 X: Type} {P: X -> Type} {S3: T3 -> Type}
  {rf0: T1 -> X} {rfG: T3 -> X}
  {G: forall n, S3 n -> P (rfG n)}
  {d1 d2: T1} {E1: d1 = d2}
  {n1 n2: T3} {D2: n1 = n2}
  {E0: rfG n1 = rf0 d1}
  {D1: rfG n2 = rf0 d2}
  {aL: P (rfG n1)} {aR: S3 n1}:
  aL = G n1 aR ->
  E0 • f_equal rf0 E1 = f_equal rfG D2 • D1 ->
  rew [fun d => P (rf0 d)] E1 in rew [P] E0 in aL
  = rew [P] D1 in G n2 (rew [S3] D2 in aR).
Proof.
  now exact (rew_cohLayer (P := P) (S2 := P) (rf0 := rf0)
    (rfF := fun x => x) (F := fun _ a => a)
    (C2C := cnil) (D2C := [: D2 :]) (KC := cnil) (C1C := [: E0 :])
    (aL := aL)).
Defined.

Lemma rew_cohLayer31 {T1 T2 X: Type} {P: X -> Type} {S2: T2 -> Type}
  {rf0: T1 -> X} {rfF: T2 -> X}
  {F: forall m, S2 m -> P (rfF m)}
  {d1 d2: T1} {E1: d1 = d2}
  {m1 m2: T2} {C2: m1 = m2}
  {C1: rfF m2 = rf0 d1}
  {D1: rfF m1 = rf0 d2}
  {aL: S2 m1} {aR: P (rfF m1)}:
  F m1 aL = aR ->
  f_equal rfF C2 • (C1 • f_equal rf0 E1) = D1 ->
  rew [fun d => P (rf0 d)] E1 in rew [P] C1 in F m2 (rew [S2] C2 in aL)
  = rew [P] D1 in aR.
Proof.
  now exact (rew_cohLayer (P := P) (S3 := P) (rf0 := rf0)
    (rfF := rfF) (rfG := fun x => x) (G := fun _ a => a)
    (m1 := m1) (C2C := [: C2 :]) (D2C := cnil) (KC := cnil) (C1C := [: C1 :])
    (D1 := D1) (aR := aR)).
Defined.
