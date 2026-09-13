(** Interpreting words by face maps.

    The action uses a [FaceStr]: a family of levels and face maps. A [wskip]
    acts by the top face followed by the rest of the word. A [wkeep] acts
    on [shiftStr], which raises the levels by one and preserves face indices.

    The exchange law [CohOf] supplies naturality of a top face along a word
    and the compositor identifying iterated action with action of a composite.
    No truncation of the levels is assumed.

    [applyWNat] takes an abstract family [T] of top faces. At a [wkeep],
    the word acts on the shifted structure while [T] remains the same family
    at the raised level; it need not be the top face of that structure. *)

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation LeSProp NatLemmas.

From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Presheaf Require Export FaceStructure.

Set Primitive Projections.
Set Printing Projections.

Section Presheaves.
Context (A: HSet).

(** The action of a word. A [wskip] at codomain [S m] deletes the top
    dimension [m]; a [wkeep] leaves it untouched, and the rest of the word
    acts on the shifted structure. *)

Fixpoint applyW (m: nat) {struct m}:
  forall n (w: Word A n m) (Q: FaceStr A), Q.(S0) m -> Q.(S0) n.
Proof.
  destruct m as [|m].
  - intros n w Q. destruct n as [|n]. now exact (fun x => x). now destruct w.
  - intros n w Q. destruct w as [(ε, w)|w].
    + now exact (fun x => applyW m n w Q (sTop Q m ε x)).
    + destruct n as [|n]. now destruct w.
      now exact (applyW m n w (shiftStr Q)).
Defined.

Lemma applyW_id {n} (Q: FaceStr A) x: applyW n n (wid n) Q x = x.
Proof.
  revert Q x; induction n as [|n IHn]; intros Q x.
  - now reflexivity.
  - now exact (IHn (shiftStr Q) x).
Defined.

End Presheaves.

Arguments applyW {A} m {n} w Q x.
Arguments applyW_id {_ _} _ _.

(** Naturality: a word commutes with a top face, at the cost of one exchange
    per deleted dimension. *)

Lemma applyWNat {A: HSet} (m: nat): forall n (w: Word A n m) (Q: FaceStr A)
  (T: forall k (ε: A), Q.(S0) (S k) -> Q.(S0) k)
  (HT: forall k q (Hq: q <= k) (ε ω: A) (X: Q.(S0) (S (S k))),
    T k ε (Q.(SFace) (S k) q (↑ Hq) ω X) = Q.(SFace) k q Hq ω (T (S k) ε X))
  (ε: A) (x: Q.(S0) (S m)),
  applyW m w Q (T m ε x) = T n ε (applyW m w (shiftStr Q) x).
Proof.
  induction m as [|m IHm]; intros n w Q T HT ε x.
  - destruct n as [|n]; [now destruct w | now destruct w].
  - destruct w as [(b, w)|w].
    + refine (_ • IHm n w Q T HT ε (sTop (shiftStr Q) m b x)).
      now exact (f_equal (applyW m w Q) (eq_sym (HT m m leR_refl ε b x))).
    + destruct n as [|n]; [now destruct w|].
      now exact (IHm n w (shiftStr Q) (fun k => T (S k))
        (fun k q Hq ε ω X => HT (S k) q (↑ Hq) ε ω X) ε x).
Defined.

(** The compositor: the action of a composite word agrees with the composite
    of the actions. *)

Lemma applyWComp {A: HSet} (p: nat): forall m n (g: Word A m p) (f: Word A n m)
  (Q: FaceStr A) (HQ: CohOf Q) (x: Q.(S0) p),
  applyW m f Q (applyW p g Q x) = applyW p (wcomp g f) Q x.
Proof.
  induction p as [|p IHp]; intros m n g f Q HQ x.
  - destruct m as [|m]; [|now destruct g].
    destruct n as [|n]; [|now destruct f].
    now destruct g, f.
  - destruct g as [(b, g)|g].
    + now exact (IHp m n g f Q HQ (sTop Q p b x)).
    + destruct m as [|m]; [now destruct g|].
      destruct f as [(a, f)|f].
      * refine (_ • IHp m n g f Q HQ (sTop Q p a x)).
        now exact (f_equal (applyW m f Q)
          (eq_sym (applyWNat p m g Q (sTop Q) (topCoh HQ) a x))).
      * destruct n as [|n]; [now destruct f|].
        now exact (IHp m n g f (shiftStr Q) (cohShift HQ) x).
Defined.

(** A generating coface acts by its face map. *)

Section Generators.
Context (A: HSet).

Lemma applyWgen (Q: FaceStr A) (n q: nat) (Hq: q <= n) (ε: A) (x: Q.(S0) (S n)):
  applyW (S n) (wgen n q ε) Q x = Q.(SFace) n q Hq ε x.
Proof.
  revert Q q Hq x; induction n as [|n IHn]; intros Q q Hq x.
  - pose proof (leR0Eq Hq) as Eq; subst q. now reflexivity.
  - destruct (Nat.eqb q (S n)) eqn:E.
    + pose proof (natEqbEq q (S n) E) as Eq; subst q.
      rewrite (wgenTop (S n) ε).
      now exact (applyW_id Q (sTop Q (S n) ε x)).
    + assert (Hq': q <= n) by now exact (leRDown q n Hq E).
      rewrite (wgenLift Hq' ε).
      now exact (IHn (shiftStr Q) q Hq' x).
Defined.

End Generators.
