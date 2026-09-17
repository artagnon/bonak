(** A few rewriting lemmas not in the standard library *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT Notation.

(** Transport along a pointwise equality commutes with transport in the
    indexing type, for any family [El] over the common codomain. *)
Lemma rew_permute_ll {S: Type} (El: S -> Type)
  (A: Type) (P Q: A -> S) (x y: A)
  (H: forall z: A, P z = Q z) (H': x = y) (a: El (P x)):
  rew [El] H y in rew [fun z => El (P z)] H' in a =
  rew [fun z => El (Q z)] H' in rew [El] H x in a.
Proof.
  now destruct H'.
Defined.

(** Transport along [p • (h • eq_sym q)] is equivalent to transporting
    both endpoints along [p] and [q] before comparing them over [h]. *)
Lemma rew_conjugate {A: Type} (P: A -> Type)
  {x x' y y': A} (p: x = x') (h: x' = y') (q: y = y')
  (u: P x) (v: P y):
  rew [P] (p • (h • eq_sym q)) in u = v ->
  rew [P] h in rew [P] p in u = rew [P] q in v.
Proof.
  intro H; rewrite <- 2 rew_compose in H.
  refine (eq_sym (rew_opp_r P q _) • _).
  now exact (f_equal (fun v => rew [P] q in v) H).
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

Lemma eq_trans_shift_l {A} {x y z: A} (p: x = y) (q: y = z) (r: x = z):
  p • q = r -> q = eq_sym p • r.
Proof.
  destruct p, q. intro H. now destruct H.
Qed.

(** Cancelling a common prefix under an inversion *)
Lemma eq_trans_sym_cancel_common {A: Type} {x y z w: A} (a: x = y) (o: y = z)
  (p: y = w):
  eq_sym (a • o) • (a • p) = eq_sym o • p.
Proof.
  now destruct a, o, p.
Qed.

(** Conjugating by a composite is conjugating twice: writing [c u v r] for
    [eq_sym u • (r • v)], this states [c aA aB P • sB = sA • c (aA • sA)
    (aB • sB) P], the form in which the two halves are met. *)
Lemma eq_trans_conj_comp {A: Type} {x0 x1 x2 y0 y1 y2: A}
  (aA: x0 = x1) (sA: x1 = x2) (P: x0 = y0) (aB: y0 = y1) (sB: y1 = y2):
  (eq_sym aA • (P • aB)) • sB = sA • (eq_sym (aA • sA) • (P • (aB • sB))).
Proof.
  now destruct aA, sA, P, aB, sB.
Qed.

Lemma eq_trans_nat_id {A} {f: A -> A} (α: forall a, f a = a) {x y: A}
  (p: x = y): α x • p = f_equal f p • α y.
Proof.
  destruct p. symmetry. apply eq_trans_refl_l.
Qed.

Lemma rew_align {A: Type} {P: A -> Type} {x x' y: A}
  {e: x = y} {e': x' = y} (b: x = x') {v: P x} {v': P x'}
  (Hv: rew [P] b in v = v') (Hcoh: e = b • e'):
  rew [P] e in v = rew [P] e' in v'.
Proof.
  destruct Hv, b. now rewrite Hcoh, eq_trans_refl_l.
Qed.

Lemma rew_sym_cancel {A: Type} {P: A -> Type} {x y: A} (e: x = y) (a: P x):
  rew [P] (eq_sym e) in rew [P] e in a = a.
Proof.
  now destruct e.
Qed.

Lemma rew_sym_cancel_r {A: Type} {P: A -> Type} {x y: A} (e: x = y)
  (b: P y): rew [P] e in rew [P] (eq_sym e) in b = b.
Proof.
  now destruct e.
Qed.

Lemma eq_sym_f_equal {A B: Type} (f: A -> B) {x y: A} (e: x = y):
  eq_sym (f_equal f e) = f_equal f (eq_sym e).
Proof.
  now destruct e.
Qed.

(** Transport in a family of path types between two maps: the
    transported path is the conjugate by the images of the base path. *)
Lemma rew_between {T U: Type} (f g: T -> U) {x y: T} (e: x = y)
  (q: f x = g x):
  rew [fun a => f a = g a] e in q =
  eq_sym (f_equal f e) • (q • f_equal g e).
Proof.
  destruct e; cbn. now rewrite eq_trans_refl_l.
Qed.

(** The case of [rew_between] where the right map is constant, so only the
    left image contributes. *)
Lemma rew_between_const_r {T U: Type} (f: T -> U) {x y: T} (e: x = y) {u: U}
  (q: f x = u):
  rew [fun a => f a = u] e in q = eq_sym (f_equal f e) • q.
Proof.
  destruct e; cbn. now rewrite eq_trans_refl_l.
Qed.

(** Fused transport-chain lemmas for layer coherence proofs

    [rew_cohLayer_hex] equates two chains of three transport steps, whose
    starting elements are identified by the painting coherence. The three
    square variants [rew_cohLayer_sq_13], [rew_cohLayer_sq_31], and
    [rew_cohLayer_sq_22] split the four transport steps between the two
    sides as 1 = 3, 3 = 1, and 2 = 2, respectively.
    A call site supplies only the two premises: the painting coherence and
    the 2-dimensional frame coherence ([UIP] in the HSet development). *)

Lemma rew_cohLayer_hex {T1 T2 T3 X: Type} {P: X -> Type}
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
(** The proof below makes path composition explicit, simplifying higher
    coherence proofs that depend on the structure of its proof term.
    An alternative proof is:

  intros HC Hpath.
  rewrite <- (map_subst F C2 aL), <- (map_subst G D2 aR), <- HC.
  destruct E1, C2, D2. cbn in Hpath |- *.
  rewrite rew_compose.
  rewrite 2 eq_trans_refl_l in Hpath.
  now rewrite Hpath.
*)
  intros HC Hpath.
  refine (rew_map P rf0 E1 _ • _).
  (** Combine the base transports, then cancel the mapped left edge. *)
  refine (rew_compose P C1 (f_equal rf0 E1) _ • _).
  refine (sigT_trans_eq_inv_l (sigT_map_eq (Q := P) F (p := C2) (u := aL) eq_refl) _).
  rewrite Hpath.
  now exact (HC ⊙ (sigT_map_eq (Q := P) G (p := D2) (u := aR) eq_refl ⊙ eq_refl)).
Defined.

(** The [rew_cohLayer*] lemmas for square-shaped coherences can be considered an
    instance of the hexagon-shaped one, with 2 arrows trivial. *)

Lemma rew_cohLayer_sq_13 {T1 T3 X: Type} {P: X -> Type} {S3: T3 -> Type}
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
  eapply (rew_cohLayer_hex (P := P) (S2 := P) (rf0 := rf0)
    (rfF := fun x => x) (F := fun _ a => a)
    (C2 := eq_refl) (C1 := eq_refl) (K := K) (aL := aL)).
  now exact HC.
  now rewrite 2 eq_trans_refl_l.
Defined.

Lemma rew_cohLayer_sq_22 {T1 T3 X: Type} {P: X -> Type} {S3: T3 -> Type}
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
  eapply (rew_cohLayer_hex (P := P) (S2 := P) (rf0 := rf0)
    (rfF := fun x => x) (F := fun _ a => a)
    (C2 := eq_refl) (C1 := E0) (K := eq_refl) (aL := aL)).
  now exact HC.
  now rewrite 2 eq_trans_refl_l.
Defined.

Lemma rew_cohLayer_sq_31 {T1 T2 X: Type} {P: X -> Type} {S2: T2 -> Type}
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
  eapply (rew_cohLayer_hex (P := P) (S3 := P) (rf0 := rf0)
    (rfF := rfF) (rfG := fun x => x) (G := fun _ a => a)
    (m1 := m1) (D2 := eq_refl) (D1 := D1) (K := eq_refl) (aR := aR)).
  now exact HC.
  now rewrite 2 eq_trans_refl_l.
Defined.
