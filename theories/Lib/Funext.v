Set Warnings "-notation-overridden".
From Bonak.Lib Require Import Logic Tactics Equiv Univalence.
Import Logic.EqNotations.


Lemma eqvPrecompInj {A B: Type} (e: Equiv A B) (C: B -> Type)
  (f g: forall y, C y) (h: (fun x => f (e x)) = (fun x => g (e x))): f = g.
Proof.
  rewrite <- (secEq (uaEquiv A B) e) in h.
  change (invEq (uaEquiv A B) e) with (ua e) in h.
  revert C f g h. destruct (ua e). now intros C f g h.
Qed.

Lemma functional_extensionality_dep {A} {B: A -> Type}
  (f g: forall x: A, B x): (forall x, f x = g x) -> f = g.
Proof.
  intro h.
  pose (E := {a: A &T B a}).
  pose (D := {a: A &T {x: B a &T {y: B a &T x = y}}}).
  pose (diag := fun t: E => ((t.1; (t.2; (t.2; eq_refl))): D)).
  pose (first := fun t: D => ((t.1; t.2.1): E)).
  assert (left: forall t, first (diag t) = t) by now intros [a x].
  assert (right: forall t, diag (first t) = t).
  { intros [a [x [y p]]]. now destruct p. }
  pose (e := qinvEquiv diag first left right).
  pose (C (t: D) := B t.1).
  pose (src := fun t: D => (t.2.1: C t)).
  pose (dst := fun t: D => (t.2.2.1: C t)).
  assert (same: src = dst) by now apply (eqvPrecompInj e C).
  pose (graph := fun a: A => ((a; (f a; (g a; h a))): D)).
  now exact (f_equal (fun (k: forall t, C t) a => k (graph a)) same).
Qed.

(** A version of [functional_extensionality_dep] which is provably equal to
    [eq_refl] on [fun _ => eq_refl] *)

Definition functional_extensionality_dep_good {A} {B: A -> Type}
  (f g: forall x: A, B x) (H: forall x, f x = g x): f = g :=
  eq_trans (eq_sym (functional_extensionality_dep f f (fun _ => eq_refl)))
    (functional_extensionality_dep f g H).

Lemma functional_extensionality_dep_good_refl {A B} f:
  @functional_extensionality_dep_good A B f f (fun _ => eq_refl) = eq_refl.
Proof.
  unfold functional_extensionality_dep_good.
  now edestruct functional_extensionality_dep.
Defined.

Opaque functional_extensionality_dep_good.

Lemma forall_sig_eq_rect {A B} (f: forall a: A, B a)
  (P: {g: forall a, B a &T forall a, f a = g a} -> Type)
  (k: P (f; fun a => eq_refl)) g: P g.
Proof.
  destruct g as [g1 g2].
  set (g' := fun x => (g1 x; g2 x): {y: B x &T f x = y}).
  change g2 with (fun x => (g' x).2).
  change g1 with (fun x => (g' x).1).
  clearbody g'; clear g1 g2.
  cut (forall x, (f x; eq_refl) = g' x).
  - intro H'. apply functional_extensionality_dep_good in H'.
    destruct H'. now exact k.
  - intro x. destruct (g' x) as [g'x1 g'x2]. now destruct g'x2.
Defined.

Definition forall_eq_rect {A B} (f: forall a: A, B a)
  (P: forall g, (forall a, f a = g a) -> Type) (k: P f (fun a => eq_refl))
  g H: P g H :=
  forall_sig_eq_rect f (fun g => P g.1 g.2) k (g; H).

Definition f_equal__functional_extensionality_dep_good {A B f g} H a:
  f_equal (fun h => h a) (@functional_extensionality_dep_good A B f g H) =
  H a.
Proof.
  apply (fun P k => forall_eq_rect _ P k _ H); clear H g.
  change (eq_refl (f a)) with (f_equal (fun h => h a) (eq_refl f)).
  apply f_equal. now apply functional_extensionality_dep_good_refl.
Defined.

(** Functional extensionality for functions out of a strict proposition.

    The lemma [functional_extensionality_dep] does not cover this case: it
    is stated at [A: Type], and [SProp] is a separate sort with no coercion into
    [Type], so [functional_extensionality_dep (A := S)] is rejected outright for
    [S: SProp].

    [sBox] removes it by giving [S] a [Type]-level carrier: a one-field
    inductive holding a proof of [S]. Ordinary funext does apply at the boxed
    domain [forall b: sBox S, T (unbox b)], and the boxed and unboxed function
    spaces transfer into each other definitionally, because [SProp] proof
    irrelevance is: any [s s': S] are convertible, hence so are [T s] and [T
    s'], and in particular [T (unbox (sbox s))] is [T s]. So [spropFunext]
    boxes, applies funext, and pulls the result back along [sbox].

    This trick is needed for *empty* [S]. Were [S] inhabited by some [s0],
    irrelevance and eta would already settle it with no axiom at all: [u] is
    convertible with [fun s => u s0], so [f_equal (fun (t: T s0) (s: S) => t) (h s0)]
    proves [u = v]. For empty [S], there is no such [s0], and the general
    statement does rest on funext. *)

Inductive sBox (S: SProp): Type := sbox: S -> sBox S.
Arguments sbox {S} _.

Definition unbox {S: SProp} (b: sBox S): S :=
  match b with sbox s => s end.

Lemma spropFunext {S: SProp} {T: S -> Type} (u v: forall s, T s)
  (h: forall s, u s = v s): u = v.
Proof.
  (* [r w] is [w] transposed to the boxed domain; the [match] typechecks
     because [T (unbox (sbox s))] is convertible with [T s]. *)
  pose (r := fun (w: forall s, T s) (b: sBox S) =>
    match b as b0 return T (unbox b0) with sbox s => w s end).
  assert (R: r u = r v).
  { apply functional_extensionality_dep_good; intros [s]. now exact (h s). }
  (* Pull back along [sbox]: [fun s => r w (sbox s)] is convertible with [w]. *)
  now exact (f_equal
    (fun (w: forall b: sBox S, T (unbox b)) (s: S) => w (sbox s)) R).
Qed.
