(** Naturality squares and hexagons with alternating mapped paths. *)

From Bonak.Lib Require Import Notation SigT.

(** Three mapped paths alternate with three connecting paths. The maps
    [f1] and [f2] occur on the left route, and [f3] on the right route.
    Each route is associated to the right. *)
Definition hexagonal_coherence {A1 A2 A3 B: Type}
  (f1: A1 -> B) (f2: A2 -> B) (f3: A3 -> B)
  {x0 x1: A1} {x2 x3: A2} {x4 x5: A3}
  (p1: x0 = x1) (p2: x2 = x3) (p3: x4 = x5)
  (h1: f1 x1 = f2 x2) (h2: f1 x0 = f3 x4) (h3: f3 x5 = f2 x3): Prop :=
  f_equal f1 p1 • (h1 • f_equal f2 p2) = h2 • (f_equal f3 p3 • h3).

(** A filler for every hexagon is equivalent to UIP. For the converse,
    take three constant maps from [unit] to [x], with all edges reflexive
    except [h2]. The hexagon reduces to [eq_refl = h2], so every loop is
    trivial. *)
Theorem hexagon_iff_UIP:
  (forall (A1 A2 A3 B: Type)
    (f1: A1 -> B) (f2: A2 -> B) (f3: A3 -> B)
    (x0 x1: A1) (x2 x3: A2) (x4 x5: A3)
    (p1: x0 = x1) (p2: x2 = x3) (p3: x4 = x5)
    (h1: f1 x1 = f2 x2) (h2: f1 x0 = f3 x4) (h3: f3 x5 = f2 x3),
    hexagonal_coherence f1 f2 f3 p1 p2 p3 h1 h2 h3) <->
  (forall (X: Type) (x y: X) (p q: x = y), p = q).
Proof.
  split.
  - intros hex X x y p q.
    destruct q.
    symmetry.
    now exact (hex unit unit unit X (fun _ => x) (fun _ => x) (fun _ => x)
      tt tt tt tt tt tt eq_refl eq_refl eq_refl eq_refl p eq_refl).
  - intros uip *.
    now apply uip.
Qed.

(** The square induced by a homotopy between two composites and a path
    in their common domain. Path actions retain the two composition steps. *)
Definition square_coherence {A B C D: Type}
  (u: A -> B) (v: A -> C) (f: B -> D) (g: C -> D)
  (K: forall x, f (u x) = g (v x)) {x y: A} (p: x = y): Prop :=
  f_equal f (f_equal u p) • K y = K x • f_equal g (f_equal v p).

(** The naturality square for a homotopy between two composites:
    Lemma 2.4.3 of the HoTT book (The Univalent Foundations Program,
    "Homotopy Type Theory: Univalent Foundations of Mathematics", 2013),
    with the equality reversed and path actions expanded through the composites. *)
Lemma square_coherence_fill {A B C D: Type}
  (u: A -> B) (v: A -> C) (f: B -> D) (g: C -> D)
  (K: forall x, f (u x) = g (v x)) {x y: A} (p: x = y):
  square_coherence u v f g K p.
Proof.
  destruct p; cbn. now exact (eq_trans_refl_l (K x)).
Defined.

(** Dependent paths around a hexagon, compared after transport along
    the chosen base coherence. The lifted routes follow the same edge
    order and association as [hexagonal_coherence]. *)
Definition hexagonal_coherence_dep {A1 A2 A3 B: Type}
  {P1: A1 -> Type} {P2: A2 -> Type} {P3: A3 -> Type} {Q: B -> Type}
  {f1: A1 -> B} {f2: A2 -> B} {f3: A3 -> B}
  (F1: forall x, P1 x -> Q (f1 x))
  (F2: forall x, P2 x -> Q (f2 x))
  (F3: forall x, P3 x -> Q (f3 x))
  {x0 x1: A1} {x2 x3: A2} {x4 x5: A3}
  {u0: P1 x0} {u1: P1 x1} {u2: P2 x2} {u3: P2 x3}
  {u4: P3 x4} {u5: P3 x5}
  {p1: x0 = x1} {p2: x2 = x3} {p3: x4 = x5}
  {h1: f1 x1 = f2 x2} {h2: f1 x0 = f3 x4} {h3: f3 x5 = f2 x3}
  (H: hexagonal_coherence f1 f2 f3 p1 p2 p3 h1 h2 h3)
  (q1: rew [P1] p1 in u0 = u1)
  (q2: rew [P2] p2 in u2 = u3)
  (q3: rew [P3] p3 in u4 = u5)
  (k1: rew [Q] h1 in F1 x1 u1 = F2 x2 u2)
  (k2: rew [Q] h2 in F1 x0 u0 = F3 x4 u4)
  (k3: rew [Q] h3 in F3 x5 u5 = F2 x3 u3): Prop :=
  rew [fun h => rew [Q] h in F1 x0 u0 = F2 x3 u3] H in
    (sigT_map_eq F1 q1 ⊙ (k1 ⊙ sigT_map_eq F2 q2)) =
  k2 ⊙ (sigT_map_eq F3 q3 ⊙ k3).

(** Dependent paths around a naturality square, compared after transport
    along the chosen base coherence. *)
Definition square_coherence_dep {A B C D: Type}
  {PA: A -> Type} {PB: B -> Type} {PC: C -> Type} {PD: D -> Type}
  (u: A -> B) (v: A -> C) (f: B -> D) (g: C -> D)
  (U: forall x, PA x -> PB (u x)) (V: forall x, PA x -> PC (v x))
  (F: forall x, PB x -> PD (f x)) (G: forall x, PC x -> PD (g x))
  (K: forall x, f (u x) = g (v x))
  (HK: forall x a, rew [PD] K x in F (u x) (U x a) = G (v x) (V x a))
  {x y: A} (p: x = y) (H: square_coherence u v f g K p)
  {a: PA x} {b: PA y} (h: rew [PA] p in a = b): Prop :=
  rew [fun e => rew [PD] e in F (u x) (U x a) = G (v y) (V y b)] H in
    (sigT_map_eq F (sigT_map_eq U h) ⊙ HK y b) =
  HK x a ⊙ sigT_map_eq G (sigT_map_eq V h).

(** A dependent homotopy lifts the canonical naturality square of its base homotopy. *)
Lemma square_coherence_dep_fill {A B C D: Type}
  {PA: A -> Type} {PB: B -> Type} {PC: C -> Type} {PD: D -> Type}
  (u: A -> B) (v: A -> C) (f: B -> D) (g: C -> D)
  (U: forall x, PA x -> PB (u x)) (V: forall x, PA x -> PC (v x))
  (F: forall x, PB x -> PD (f x)) (G: forall x, PC x -> PD (g x))
  (K: forall x, f (u x) = g (v x))
  (HK: forall x a, rew [PD] K x in F (u x) (U x a) = G (v x) (V x a))
  {x y: A} (p: x = y) {a: PA x} {b: PA y} (h: rew [PA] p in a = b):
  square_coherence_dep u v f g U V F G K HK p
    (square_coherence_fill u v f g K p) h.
Proof.
  unfold square_coherence_dep.
  destruct p, h; cbn.
  generalize (HK x a).
  generalize (K x), (G (v x) (V x a)).
  generalize (g (v x)).
  intros z k w hk.
  now destruct hk, k.
Defined.
