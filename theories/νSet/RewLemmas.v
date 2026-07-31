(** A few rewriting lemmas not in the standard library *)

From Stdlib Require Import Logic.FunctionalExtensionality.

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
Defined.

Lemma rew_app_rl A (P: A -> Type) (x y: A) (H H': x = y) (a: P x):
  H = H' -> rew <- [P] H in rew [P] H' in a = a.
Proof.
  intros * ->. now destruct H'.
Defined.

Lemma map_subst_app {A B} {x y} {𝛉: A} (H: x = y :> B) (P: A -> B -> Type)
  (f: forall 𝛉, P 𝛉 x):
  rew [P 𝛉] H in f 𝛉 = (rew [fun x => forall 𝛉, P 𝛉 x] H in f) 𝛉.
Proof.
  now destruct H.
Defined.

(** The pointwise-to-layer bridge: a layer is a dependent function over the
    arity, so transporting a layer along a path in the frame is determined
    pointwise ([functional_extensionality_dep] followed by
    [map_subst_app]). *)

Lemma layer_rew_eq {A T X: Type} {P: X -> Type} {rf0: A -> T -> X}
  {d1 d2: T} {E1: d1 = d2}
  {l: forall ω, P (rf0 ω d1)} {l': forall ω, P (rf0 ω d2)}:
  (forall ω, rew [fun d => P (rf0 ω d)] E1 in l ω = l' ω) ->
  rew [fun d => forall ω, P (rf0 ω d)] E1 in l = l'.
Proof.
  intro H. apply functional_extensionality_dep; intro ω.
  rewrite <- (map_subst_app E1 (fun ω d => P (rf0 ω d)) l).
  now exact (H ω).
Defined.

(** Fused transport-chain lemmas for layer coherence proofs

    [rew_cohLayer<NM>] closes a layer coherence goal in one step, once
    [layer_rew_eq] has taken the pointwise step: it equates two chains of
    transports, N on the left-hand side and M on the right, whose starting
    elements are identified by the painting coherence. A call site supplies
    only the two premises: the painting coherence and the 2-dimensional frame
    coherence ([UIP] in HSet development). *)

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
  rew [P] K in F m1 aL = G n1 aR -> (* painting coherence *)
  f_equal rfF C2 • (C1 • f_equal rf0 E1) = K • (f_equal rfG D2 • D1) ->
  (* 2-dimensional frame coherence, UIP for HSets *)
  rew [fun d => P (rf0 d)] E1 in rew [P] C1 in F m2 (rew [S2] C2 in aL)
  = rew [P] D1 in G n2 (rew [S3] D2 in aR).
Proof.
  intros HC Hpath.
  rewrite <- (map_subst F C2 aL), <- (map_subst G D2 aR), <- HC.
  destruct E1, C2, D2. cbn in Hpath |- *.
  rewrite rew_compose.
  rewrite 2 eq_trans_refl_l in Hpath.
  now rewrite Hpath.
Defined.

(** The [rew_cohLayer*] lemmas for square-shaped coherences can be considered an
    instance of the hexagon-shaped one, with 2 arrows trivial. *)

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
  intros HC Hpath.
  eapply (rew_cohLayer33 (P := P) (S2 := P) (rf0 := rf0)
    (rfF := fun x => x) (F := fun _ a => a)
    (C2 := eq_refl) (C1 := eq_refl) (K := K) (aL := aL)).
  now exact HC.
  now rewrite 2 eq_trans_refl_l.
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
  intros HC Hpath.
  eapply (rew_cohLayer33 (P := P) (S2 := P) (rf0 := rf0)
    (rfF := fun x => x) (F := fun _ a => a)
    (C2 := eq_refl) (C1 := E0) (K := eq_refl) (aL := aL)).
  now exact HC.
  now rewrite 2 eq_trans_refl_l.
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
  intros HC Hpath.
  eapply (rew_cohLayer33 (P := P) (S3 := P) (rf0 := rf0)
    (rfF := rfF) (rfG := fun x => x) (G := fun _ a => a)
    (m1 := m1) (D2 := eq_refl) (D1 := D1) (K := eq_refl) (aR := aR)).
  now exact HC.
  now rewrite 2 eq_trans_refl_l.
Defined.
