(** Pasting path comparisons, squares, and layer-coherence cells,
    with their dependent lifts. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT Notation RewLemmas.

(** Whiskering composes each boundary of a 2-cell with a fixed path.
    Composition is written in traversal order. *)
Definition whisker_l {X: Type} {x y z: X} (p: x = y)
  {q q': y = z} (H: q = q'): p • q = p • q' :=
  f_equal (fun q => p • q) H.

Definition whisker_r {X: Type} {x y z: X}
  {p p': x = y} (H: p = p') (q: y = z): p • q = p' • q :=
  f_equal (fun p => p • q) H.

(** Paste two edge comparisons and assemble their dependent components. *)
Definition sigT_path_paste {A: Type} {P: A -> Type}
  {x y z: A} {u: P x} {v: P y} {w: P z}
  {p: x = y} {q: y = z}
  {h: rew [P] p in u = v} {k: rew [P] q in v = w}
  {a: (x; u) = (y; v)} {b: (y; v) = (z; w)}
  (H: a = (= p; h)) (K: b = (= q; k)):
  a • b = (= p • q; h ⊙ k) :=
  (whisker_r H b • whisker_l (= p; h) K)
  • eq_trans_eq_existT_curried p h q k.

(** Transport through a pasting first transports the two component paths,
    then applies the comparison assembling their composite pair path. *)
Lemma sigT_path_paste_dep {A: Type} {P: A -> Type}
  (R: {x: A &T P x} -> Type)
  {x y z: A} {u: P x} {v: P y} {w: P z}
  {p: x = y} {q: y = z}
  {h: rew [P] p in u = v} {k: rew [P] q in v = w}
  {a: (x; u) = (y; v)} {b: (y; v) = (z; w)}
  (H: a = (= p; h)) (K: b = (= q; k))
  {r: R (x; u)} {s: R (y; v)} {t: R (z; w)}
  (ha: rew [R] a in r = s) (hb: rew [R] b in s = t):
  rew [fun e => rew [R] e in r = t] sigT_path_paste H K in (ha ⊙ hb) =
  rew [fun e => rew [R] e in r = t] eq_trans_eq_existT_curried p h q k in
    ((rew [fun e => rew [R] e in r = s] H in ha) ⊙
     (rew [fun e => rew [R] e in s = t] K in hb)).
Proof.
  subst a b. unfold sigT_path_paste.
  cbn [whisker_l whisker_r f_equal].
  now rewrite eq_trans_refl_l.
Defined.

(** Pasting squares written [p • c = a • q], with horizontal edges [a, c]
    and vertical edges [p, q]. *)
Definition square_compose {X: Type} {x0 x1 x2 y0 y1 y2: X}
  {a: x0 = x1} {b: x1 = x2} {c: y0 = y1} {d: y1 = y2}
  {p: x0 = y0} {q: x1 = y1} {r: x2 = y2}
  (H: p • c = a • q) (K: q • d = b • r):
  p • (c • d) = (a • b) • r :=
  eq_trans_assoc p c d •
  (whisker_r H d •
  (eq_sym (eq_trans_assoc a q d) •
  (whisker_l a K • eq_trans_assoc a b r))).

(** Stack two squares along their common horizontal edge. *)
Definition square_stack {X: Type} {x0 x1 y0 y1 z0 z1: X}
  {a: x0 = x1} {c: y0 = y1} {d: z0 = z1}
  {p: x0 = y0} {q: x1 = y1} {r: y0 = z0} {s: y1 = z1}
  (H: p • c = a • q) (K: r • d = c • s):
  (p • r) • d = a • (q • s) :=
  eq_sym (eq_trans_assoc p r d) •
  (whisker_l p K •
  (eq_trans_assoc p c s •
  (whisker_r H s •
  eq_sym (eq_trans_assoc a q s)))).

(** Map a square, using the comparison between mapped composites and
    composites of mapped paths on both boundaries. *)
Definition square_map {X Y: Type} (f: X -> Y) {x0 x1 y0 y1: X}
  {a: x0 = x1} {b: y0 = y1} {p: x0 = y0} {q: x1 = y1}
  (H: p • b = a • q):
  f_equal f p • f_equal f b = f_equal f a • f_equal f q :=
  eq_sym (eq_trans_map_distr f p b) •
    (f_equal (fun h => f_equal f h) H • eq_trans_map_distr f a q).

(** The naturality square for a homotopy between two composites:
    Lemma 2.4.3 of the HoTT book (The Univalent Foundations Program,
    "Homotopy Type Theory: Univalent Foundations of Mathematics", 2013),
    with the equality reversed and path actions expanded through the composites. *)
Lemma f_equal_naturality {A B C D: Type}
  (u: A -> B) (v: A -> C) (f: B -> D) (g: C -> D)
  (K: forall x, f (u x) = g (v x)) {x y: A} (p: x = y):
  f_equal f (f_equal u p) • K y = K x • f_equal g (f_equal v p).
Proof.
  destruct p; cbn. now exact (eq_trans_refl_l (K x)).
Defined.

(** Dependent paths respect square pasting. *)
Lemma square_compose_dep {X: Type} (P: X -> Type) {x0 x1 x2 y0 y1 y2: X}
  {a: x0 = x1} {b: x1 = x2} {c: y0 = y1} {d: y1 = y2}
  {p: x0 = y0} {q: x1 = y1} {r: x2 = y2}
  (H: p • c = a • q) (K: q • d = b • r)
  {u0: P x0} {u1: P x1} {u2: P x2} {v0: P y0} {v1: P y1} {v2: P y2}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in u1 = u2)
  (hc: rew [P] c in v0 = v1) (hd: rew [P] d in v1 = v2)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (hr: rew [P] r in u2 = v2)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hc) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in u1 = v2] K in (hq ⊙ hd) = hb ⊙ hr):
  rew [fun e => rew [P] e in u0 = v2] square_compose H K in
    (hp ⊙ (hc ⊙ hd)) = (ha ⊙ hb) ⊙ hr.
Proof.
  destruct p, q, r, hp, hq, hr. cbn in H, K. destruct H, K.
  destruct c, d.
  cbn [square_compose whisker_l whisker_r eq_trans_assoc f_equal eq_sym eq_trans eq_rect] in *.
  rewrite 8 sigT_trans_eq_refl, eq_trans_refl_l, eq_trans_refl_r in *.
  now rewrite HH, KK.
Defined.

(** A commuting cube transfers a dependent equality between opposite edges.
    Its base coherence compares the two pastings around the cube. *)
Lemma square_cube_dep {X: Type} (P: X -> Type) {x0 x1 y0 y1: X}
  {a a': x0 = x1} {b b': y0 = y1} {p: x0 = y0} {q: x1 = y1}
  (H: p • b = a • q) (K: p • b' = a' • q) (κ: b = b') (λ: a = a')
  (C: H • whisker_r λ q = whisker_l p κ • K)
  {u0: P x0} {u1: P x1} {v0: P y0} {v1: P y1}
  (ha: rew [P] a in u0 = u1) (ha': rew [P] a' in u0 = u1)
  (hb: rew [P] b in v0 = v1) (hb': rew [P] b' in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in (hp ⊙ hb) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in u0 = v1] K in (hp ⊙ hb') = ha' ⊙ hq)
  (D: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'):
  rew [fun e => rew [P] e in v0 = v1] κ in hb = hb'.
Proof.
  unfold whisker_l, whisker_r in C.
  destruct p, q, hp, hq. cbn in H, K. destruct H, K.
  destruct κ, b.
  cbn [f_equal eq_trans] in C.
  rewrite f_equal_id, eq_trans_refl_l in C.
  rewrite C in D.
  cbn in D.
  rewrite sigT_trans_eq_refl in HH, KK.
  cbn in HH, KK |- *.
  rewrite eq_trans_refl_l in HH, KK.
  rewrite HH, KK. now rewrite D.
Defined.

(** Pasting when the lower edges are images under a map. *)
Definition square_compose_map {X Y: Type} (f: Y -> X)
  {x0 x1 x2: X} {y0 y1 y2: Y}
  {a: x0 = x1} {b: x1 = x2} {c: y0 = y1} {d: y1 = y2}
  {p: x0 = f y0} {q: x1 = f y1} {r: x2 = f y2}
  (H: p • f_equal f c = a • q) (K: q • f_equal f d = b • r):
  p • f_equal f (c • d) = (a • b) • r :=
  whisker_l p (eq_trans_map_distr f c d) • square_compose H K.

Lemma square_compose_map_dep {X Y: Type} (f: Y -> X) (P: X -> Type)
  {x0 x1 x2: X} {y0 y1 y2: Y}
  {a: x0 = x1} {b: x1 = x2} {c: y0 = y1} {d: y1 = y2}
  {p: x0 = f y0} {q: x1 = f y1} {r: x2 = f y2}
  (H: p • f_equal f c = a • q) (K: q • f_equal f d = b • r)
  {u0: P x0} {u1: P x1} {u2: P x2}
  {v0: P (f y0)} {v1: P (f y1)} {v2: P (f y2)}
  (ha: rew [P] a in u0 = u1) (hb: rew [P] b in u1 = u2)
  (hc: rew [fun y => P (f y)] c in v0 = v1)
  (hd: rew [fun y => P (f y)] d in v1 = v2)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (hr: rew [P] r in u2 = v2)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in
    (hp ⊙ sigT_map_eq (Q := P) (fun _ u => u) hc) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in u1 = v2] K in
    (hq ⊙ sigT_map_eq (Q := P) (fun _ u => u) hd) = hb ⊙ hr):
  rew [fun e => rew [P] e in u0 = v2] square_compose_map f H K in
    (hp ⊙ sigT_map_eq (Q := P) (fun _ u => u) (hc ⊙ hd)) = (ha ⊙ hb) ⊙ hr.
Proof.
  unfold square_compose_map, whisker_l.
  rewrite <- (rew_compose (fun e => rew [P] e in u0 = v2)
    (f_equal (fun e => p • e) (eq_trans_map_distr f c d)) (square_compose H K) _).
  rewrite <- (rew_map (fun e => rew [P] e in u0 = v2) (fun e => p • e) _ _).
  rewrite rew_sigT_trans_eq_r.
  rewrite (sigT_map_eq_comp (Q := P) (fun _ u => u) hc hd).
  now exact (square_compose_dep P H K ha hb
    (sigT_map_eq (Q := P) (fun _ u => u) hc)
    (sigT_map_eq (Q := P) (fun _ u => u) hd) hp hq hr HH KK).
Defined.

Lemma square_cube_map_dep {X Y: Type} (f: Y -> X) (P: X -> Type)
  {x0 x1: X} {y0 y1: Y}
  {a a': x0 = x1} {b b': y0 = y1} {p: x0 = f y0} {q: x1 = f y1}
  (H: p • f_equal f b = a • q) (K: p • f_equal f b' = a' • q)
  (κ: b = b') (λ: a = a')
  (C: H • whisker_r λ q =
      whisker_l p (f_equal (fun e => f_equal f e) κ) • K)
  {u0: P x0} {u1: P x1} {v0: P (f y0)} {v1: P (f y1)}
  (ha: rew [P] a in u0 = u1) (ha': rew [P] a' in u0 = u1)
  (hb: rew [fun y => P (f y)] b in v0 = v1)
  (hb': rew [fun y => P (f y)] b' in v0 = v1)
  (hp: rew [P] p in u0 = v0) (hq: rew [P] q in u1 = v1)
  (HH: rew [fun e => rew [P] e in u0 = v1] H in
    (hp ⊙ sigT_map_eq (Q := P) (fun _ u => u) hb) = ha ⊙ hq)
  (KK: rew [fun e => rew [P] e in u0 = v1] K in
    (hp ⊙ sigT_map_eq (Q := P) (fun _ u => u) hb') = ha' ⊙ hq)
  (D: rew [fun e => rew [P] e in u0 = u1] λ in ha = ha'):
  rew [fun e => rew [fun y => P (f y)] e in v0 = v1] κ in hb = hb'.
Proof.
  apply (sigT_map_eq_id_inj f P).
  pose proof (square_cube_dep P H K (f_equal (fun e => f_equal f e) κ) λ C
    ha ha' (sigT_map_eq (Q := P) (fun _ u => u) hb)
    (sigT_map_eq (Q := P) (fun _ u => u) hb') hp hq HH KK D) as E.
  rewrite <- (rew_map (fun e => rew [P] e in v0 = v1)
    (fun e => f_equal f e) κ _) in E.
  rewrite (map_subst
    (fun e (h: rew [fun y => P (f y)] e in v0 = v1) =>
      sigT_map_eq (Q := P) (fun _ u => u) h) κ hb) in E.
  now exact E.
Defined.

(** Map a layer-coherence cell, then use the naturality of [α] to identify
    its transported endpoints. *)
Definition layer_square_map
  {T M N X Y U: Type} (r: T -> X) (s: M -> X) (t: N -> X)
  (f: X -> Y) (g: T -> U) (j: U -> Y)
  (α: forall d, f (r d) = j (g d))
  {d d': T} (e: d = d') {m m': M} (p: m = m') {n n': N} (q: n = n')
  (v: s m' = r d) (w: t n' = r d') (k: s m = t n)
  (H: f_equal s p • (v • f_equal r e) = k • (f_equal t q • w))
  (Hnat: f_equal f (f_equal r e) • α d' = α d • f_equal j (f_equal g e)):
  (f_equal f (f_equal s p • v) • α d) • f_equal j (f_equal g e) =
  f_equal f k • (f_equal f (f_equal t q • w) • α d').
Proof.
  now exact (square_stack
    (square_map f (eq_sym (eq_trans_assoc _ _ _) • H)) (eq_sym Hnat)).
Defined.

Lemma layer_square_map_dep
  {T M N X Y U: Type} (r: T -> X) (s: M -> X) (t: N -> X)
  (f: X -> Y) (g: T -> U) (j: U -> Y)
  (α: forall d, f (r d) = j (g d))
  (P: X -> Type) (Q: Y -> Type) (PM: M -> Type) (PN: N -> Type)
  (F: forall x, P x -> Q (f x))
  (L: forall m, PM m -> P (s m)) (R: forall n, PN n -> P (t n))
  {d d': T} (e: d = d') {m m': M} (p: m = m') {n n': N} (q: n = n')
  (v: s m' = r d) (w: t n' = r d') (k: s m = t n)
  (H: f_equal s p • (v • f_equal r e) = k • (f_equal t q • w))
  {a: PM m} {b: PN n} (h: rew [P] k in L m a = R n b):
  rew [fun e => rew [Q] e in F (s m) (L m a) =
    rew [Q] α d' in F (r d') (rew [P] w in R n' (rew [PN] q in b))]
    layer_square_map r s t f g j α e p q v w k H
      (f_equal_naturality r g f j α e) in
  ((sigT_map_eq F (sigT_map_eq L (p := p) (u := a) eq_refl ⊙ eq_refl) ⊙ eq_refl)
    ⊙ sigT_map_eq (Q := Q) (fun _ u => u)
      (sigT_map_eq (Q := fun u => Q (j u))
        (fun dd x => rew [Q] α dd in F (r dd) x)
        (rew_cohLayer_hex (P := P) (rf0 := r) (F := L) (G := R)
          (E1 := e) (C2 := p) (D2 := q) (C1 := v) (D1 := w) h H))) =
  sigT_map_eq F h ⊙
    (sigT_map_eq F (sigT_map_eq R (p := q) (u := b) eq_refl ⊙ eq_refl) ⊙ eq_refl).
Proof.
  destruct p, q, e.
  cbn [eq_rect f_equal] in H |- *.
  unfold layer_square_map.
  unfold rew_cohLayer_hex.
  cbn.
  rewrite 2 sigT_map_eq_refl.
  revert H h.
  generalize (L m a), (R n b).
  revert k v w.
  generalize (α d).
  generalize (j (g d)).
  generalize (r d), (s m), (t n).
  intros z x y z' γ k v w u v' H h.
  destruct w, v. cbn in H. now destruct H, h, γ.
Defined.

(** The layer-coherence path fills its defining square. *)
Lemma layer_square {V W X: Type} {S: V -> Type} {P: X -> Type}
  (f g: V -> X) (d: W -> X)
  (F: forall v, S v -> P (f v)) (G: forall v, S v -> P (g v))
  {m1 m2 n1 n2: V} (l: m1 = m2) (r: n1 = n2)
  {w1 w2: W} (e: w1 = w2)
  (c: f m2 = d w1) (c': g n2 = d w2) (k: f m1 = g n1)
  {a: S m1} {b: S n1} (h: rew [P] k in F m1 a = G n1 b)
  (H: f_equal f l • (c • f_equal d e) = k • (f_equal g r • c')):
  rew [fun e => rew [P] e in F m1 a = rew [P] c' in G n2 (rew [S] r in b)]
    (eq_sym (eq_trans_assoc _ _ _) • H) in
    ((sigT_map_eq F (p := l) (u := a) eq_refl ⊙ eq_refl) ⊙
      sigT_map_eq (Q := P) (fun _ u => u)
       (rew_cohLayer_hex (P := P) (rf0 := d) (F := F) (G := G) (E1 := e)
         (C2 := l) (D2 := r) (C1 := c) (D1 := c') h H)) =
    h ⊙ (sigT_map_eq G (p := r) (u := b) eq_refl ⊙ eq_refl).
Proof.
  rewrite (sigT_map_eq_id (P := P) d).
  unfold rew_cohLayer_hex.
  rewrite eq_trans_sym_cancel_l.
  now apply sigT_square_fill_boundary.
Defined.

(** Extend a layer-coherence cell along a path in its source, using the
    naturality of the frame and dependent-path coherences. *)
Definition layer_square_nat {Z V W X: Type}
  (L R: Z -> V) (f g: V -> X) (d: W -> X)
  (k: forall z, f (L z) = g (R z))
  {z1 z2: Z} (p: z1 = z2)
  {m n: V} (l: L z2 = m) (r: R z2 = n)
  {w1 w2: W} (e: w1 = w2)
  (c: f m = d w1) (c': g n = d w2)
  (H: f_equal f l • (c • f_equal d e) = k z2 • (f_equal g r • c'))
  (Hnat: f_equal f (f_equal L p) • k z2 = k z1 • f_equal g (f_equal R p)):
  (f_equal f (f_equal L p • l) • c) • f_equal d e =
    k z1 • (f_equal g (f_equal R p • r) • c').
Proof.
  refine (f_equal (fun h => (h • c) • f_equal d e)
    (eq_trans_map_distr f _ _) • _).
  refine (whisker_r (eq_sym (eq_trans_assoc _ _ _)) (f_equal d e) • _).
  refine (square_stack Hnat (eq_sym (eq_trans_assoc _ _ _) • H) • _).
  refine (whisker_l (k z1) _).
  refine (eq_trans_assoc _ _ _ • _).
  now exact (whisker_r (eq_sym (eq_trans_map_distr g _ _)) c').
Defined.

Lemma layer_square_nat_dep {Z V W X: Type}
  {S: Z -> Type} {Q: V -> Type} {P: X -> Type}
  (L R: Z -> V) (f g: V -> X) (d: W -> X)
  (RL: forall z, S z -> Q (L z)) (RR: forall z, S z -> Q (R z))
  (F: forall v, Q v -> P (f v)) (G: forall v, Q v -> P (g v))
  (k: forall z, f (L z) = g (R z))
  (hk: forall z a, rew [P] k z in F (L z) (RL z a) = G (R z) (RR z a))
  {z1 z2: Z} (p: z1 = z2)
  {m n: V} (l: L z2 = m) (r: R z2 = n)
  {w1 w2: W} (e: w1 = w2)
  (c: f m = d w1) (c': g n = d w2)
  (H: f_equal f l • (c • f_equal d e) = k z2 • (f_equal g r • c'))
  (a: S z1):
  rew [fun e => rew [P] e in F (L z1) (RL z1 a) =
    rew [P] c' in G n (rew [Q] r in RR z2 (rew [S] p in a))]
    layer_square_nat L R f g d k p l r e c c' H
      (f_equal_naturality L R f g k p) in
    ((sigT_map_eq F
       (sigT_map_eq RL (p := p) (u := a) eq_refl ⊙
         (eq_refl: rew [Q] l in RL z2 (rew [S] p in a) = _)) ⊙ eq_refl) ⊙
     sigT_map_eq (Q := P) (fun _ u => u)
       (rew_cohLayer_hex (P := P) (rf0 := d) (F := F) (G := G) (E1 := e)
          (C2 := l) (D2 := r) (C1 := c) (D1 := c')
          (hk z2 (rew [S] p in a)) H)) =
    hk z1 a ⊙
      (sigT_map_eq G
        (sigT_map_eq RR (p := p) (u := a) eq_refl ⊙
          (eq_refl: rew [Q] r in RR z2 (rew [S] p in a) = _)) ⊙ eq_refl).
Proof.
  destruct p, l, r.
  refine (_ • layer_square f g d F G eq_refl eq_refl e c c' (k z1) (hk z1 a) H).
  apply f_equal.
  unfold layer_square_nat, f_equal_naturality, square_stack.
  cbn in H |- *.
  generalize H; clear H.
  generalize (k z1), c, c', (f_equal d e).
  generalize (f (L z1)), (g (R z1)), (d w1), (d w2).
  intros x y z t K C C' E H0.
  destruct C, C', E; cbn in H0.
  now destruct H0.
Defined.

(** Changing the endpoints of a dependent path. Each correction goes from
    the new endpoint to the old one. *)
Definition dpath_change {X: Type} {P: X -> Type} {x y: X} {p: x = y}
  {a a': P x} {b b': P y} (s: a' = a)
  (h: rew [P] p in a = b) (t: b' = b):
  rew [P] p in a' = b' :=
  f_equal (fun a => rew [P] p in a) s • (h • eq_sym t).

(** The two copies of the middle endpoint correction cancel in a composite. *)
Lemma dpath_change_comp {X: Type} {P: X -> Type} {x y z: X} {p: x = y} {q: y = z}
  {a a': P x} {b b': P y} {c c': P z}
  (s: a' = a) (t: b' = b) (u: c' = c)
  (h: rew [P] p in a = b) (k: rew [P] q in b = c):
  dpath_change s h t ⊙ dpath_change t k u = dpath_change s (h ⊙ k) u.
Proof.
  destruct s, t, u. unfold dpath_change; cbn [f_equal eq_sym].
  now rewrite 3 eq_trans_refl_l, 3 eq_trans_refl_r.
Defined.

Lemma dpath_change_map {X Y: Type} {P: X -> Type} {Q: Y -> Type} {f: X -> Y}
  (g: forall x, P x -> Q (f x)) {x y: X} {p: x = y}
  {a a': P x} {b b': P y} (s: a' = a) (t: b' = b)
  (h: rew [P] p in a = b):
  sigT_map_eq g (dpath_change s h t) =
  dpath_change (f_equal (g x) s) (sigT_map_eq g h) (f_equal (g y) t).
Proof.
  destruct s, t. unfold dpath_change; cbn [f_equal eq_sym].
  now rewrite 2 eq_trans_refl_l, 2 eq_trans_refl_r.
Defined.

Lemma dpath_change_cell {X: Type} {P: X -> Type} {x y: X} {p q: x = y}
  {a a': P x} {b b': P y} (s: a' = a) (t: b' = b) (K: p = q)
  (h: rew [P] p in a = b) (k: rew [P] q in a = b):
  rew [fun e => rew [P] e in a = b] K in h = k ->
  rew [fun e => rew [P] e in a' = b'] K in dpath_change s h t =
  dpath_change s k t.
Proof.
  intro H. refine (map_subst (fun e h => dpath_change s h t) K h • _).
  now exact (f_equal (fun h => dpath_change s h t) H).
Defined.

Lemma dpath_change_natural {X A: Type} {P: X -> Type} {x y: X} {p: x = y}
  (f: A -> P x) (g: A -> P y) (H: forall a, rew [P] p in f a = g a)
  {a a': A} (s: a' = a):
  dpath_change (f_equal f s) (H a) (f_equal g s) = H a'.
Proof.
  unfold dpath_change.
  rewrite eq_trans_assoc.
  rewrite (f_equal_naturality f g (fun v => rew [P] p in v) (fun v => v) H s).
  rewrite f_equal_id, <- eq_trans_assoc, eq_trans_sym_inv_r.
  now apply eq_trans_refl_r.
Defined.

(** Successive changes of endpoints compose their correction paths. *)
Lemma dpath_change_nest {X: Type} {P: X -> Type} {x y: X} {p: x = y}
  {a a' a'': P x} {b b' b'': P y}
  (s: a' = a) (s': a'' = a') (t: b' = b) (t': b'' = b')
  (h: rew [P] p in a = b):
  dpath_change s' (dpath_change s h t) t' =
  dpath_change (s' • s) h (t' • t).
Proof.
  destruct s', s, t', t. unfold dpath_change; cbn [f_equal eq_sym].
  now rewrite 4 eq_trans_refl_l, 3 eq_trans_refl_r.
Defined.

Lemma dpath_change_id {X: Type} {P: X -> Type} {x y: X} {p: x = y}
  {a: P x} {b: P y} (h: rew [P] p in a = b):
  dpath_change eq_refl h eq_refl = h.
Proof.
  unfold dpath_change; cbn [f_equal eq_sym].
  now rewrite eq_trans_refl_l, eq_trans_refl_r.
Defined.

Lemma dpath_change_refl {X: Type} {P: X -> Type} {x y: X} (p: x = y)
  (a: P x) {b: P y} (t: b = rew [P] p in a):
  dpath_change (p := p) eq_refl eq_refl t = eq_sym t.
Proof.
  unfold dpath_change; cbn [f_equal]. now rewrite 2 eq_trans_refl_l.
Defined.

(** A transported identity square changes both endpoints by the same path. *)
Lemma dpath_change_transport {X: Type} {P: X -> Type} {x y: X} (p: x = y)
  {a a': P x} (s: a' = a) {b: P y} (t: b = rew [P] p in a'):
  dpath_change s (p := p) eq_refl
    (t • f_equal (fun a => rew [P] p in a) s) = eq_sym t.
Proof.
  destruct s. cbn [f_equal].
  rewrite eq_trans_refl_r. now apply dpath_change_refl.
Defined.

(** A dependent map over a fixed base acts on paths without reindexing the base. *)
Definition dpath_map {X: Type} {P Q: X -> Type} (g: forall x, P x -> Q x)
  {x y: X} {p: x = y} {a: P x} {b: P y} (h: rew [P] p in a = b):
  rew [Q] p in g x a = g y b :=
  map_subst g p a • f_equal (g y) h.

Lemma dpath_map_comp {X: Type} {P Q: X -> Type} (g: forall x, P x -> Q x)
  {x y z: X} {p: x = y} {q: y = z} {a: P x} {b: P y} {c: P z}
  (h: rew [P] p in a = b) (k: rew [P] q in b = c):
  dpath_map g (h ⊙ k) = dpath_map g h ⊙ dpath_map g k.
Proof.
  now destruct p, q, h, k.
Defined.

(** A square of dependent maps commutes on paths, with its endpoint squares. *)
Lemma dpath_map_square {X Y: Type} {P P': X -> Type} {Q Q': Y -> Type} {f: X -> Y}
  (e: forall x, P x -> P' x) (e': forall y, Q y -> Q' y)
  (g: forall x, P x -> Q (f x)) (g': forall x, P' x -> Q' (f x))
  (N: forall x a, e' (f x) (g x a) = g' x (e x a))
  {x y: X} {p: x = y} {a: P x} {b: P y} (h: rew [P] p in a = b):
  dpath_map e' (sigT_map_eq g h) =
  dpath_change (N x a) (sigT_map_eq g' (dpath_map e h)) (N y b).
Proof.
  destruct p, h. unfold dpath_map, dpath_change; cbn.
  now rewrite eq_trans_refl_l, f_equal_id, eq_trans_sym_inv_r.
Defined.

(** Separating the reindexing of the base from the action in each fibre. *)
Lemma sigT_map_eq_dpath_map {X Y: Type} {P: X -> Type} {Q: Y -> Type} {f: X -> Y}
  (g: forall x, P x -> Q (f x)) {x y: X} {p: x = y}
  {a: P x} {b: P y} (h: rew [P] p in a = b):
  sigT_map_eq g h = eq_sym (rew_map Q f p (g x a)) • dpath_map g h.
Proof.
  now destruct p, h.
Defined.
