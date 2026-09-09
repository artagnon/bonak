(** Generating cofaces and coordinate deletions of the ν-shape category. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Notation LeSProp NatLemmas.
From Bonak.Category Require Import Category.
From Bonak.Presheaf.Dgn Require Export νShape.
Set Primitive Projections.
Set Printing Projections.

Section Generators.
Context {A: HSet}.

Lemma shapeCompKeep {p m n} (f: Shape A p m) (g: Shape A m n):
  shapeComp (shapeKeep f) (shapeKeep g) = shapeKeep (shapeComp f g).
Proof. destruct f as [i [r f]], g as [j [s g]]. reflexivity. Qed.

Lemma shapeCompDrop {p m n} (f: Shape A p m) (g: Shape A m n):
  shapeComp (shapeDrop f) g = shapeDrop (shapeComp f g).
Proof. destruct f as [i [r f]], g as [j [s g]]. reflexivity. Qed.

Lemma shapeCompConst {p m n} (f: Shape A p m) (g: Shape A m n) (a: A):
  shapeComp f (shapeConst a g) = shapeConst a (shapeComp f g).
Proof. destruct f as [i [r f]], g as [j [s g]]. reflexivity. Qed.

Lemma shapeCompKeepDrop {p m n} (f: Shape A p m) (g: Shape A m n):
  shapeComp (shapeKeep f) (shapeDrop g) = shapeDrop (shapeComp f g).
Proof. destruct f as [i [r f]], g as [j [s g]]. reflexivity. Qed.

Lemma shapeCompConstKeep {p m n} (f: Shape A p m) (g: Shape A m n) (a: A):
  shapeComp (shapeConst a f) (shapeKeep g) = shapeConst a (shapeComp f g).
Proof. destruct f as [i [r f]], g as [j [s g]]. reflexivity. Qed.

Lemma shapeCompConstDrop {p m n} (f: Shape A p m) (g: Shape A m n) (a: A):
  shapeComp (shapeConst a f) (shapeDrop g) = shapeComp f g.
Proof. destruct f as [i [r f]], g as [j [s g]]. reflexivity. Qed.

Lemma shapeFaceComp {p m n} (f: Word A p m) (g: Word A m n):
  shapeComp (shapeFace f) (shapeFace g) = shapeFace (wcomp g f).
Proof.
  unfold shapeComp, shapeFace; cbn. rewrite crossIdR.
  unfold shapeSandwich, shapeFace; cbn. rewrite wcompIdl. reflexivity.
Qed.

Lemma shapeMaskComp {p m n} (r: Word hunit m p) (s: Word hunit n m):
  shapeComp (shapeMask r) (shapeMask s) = (shapeMask (A := A) (wcomp r s)).
Proof.
  unfold shapeComp, shapeMask; cbn. rewrite crossIdL.
  unfold shapeSandwich, shapeMask; cbn. rewrite wcompIdl. reflexivity.
Qed.

Lemma shapeFactor {p n k} (r: Word hunit k p) (f: Word A k n):
  shapeComp (shapeMask r) (shapeFace f) = (k; (r, f)).
Proof.
  unfold shapeComp, shapeMask, shapeFace; cbn. rewrite crossIdR.
  unfold shapeSandwich, shapeFace; cbn. rewrite !wcompIdr. reflexivity.
Qed.

Definition semiShapeInclusion: Functor (νSemiShape A) (νShape A) :=
  Build_Functor (νSemiShape A) (νShape A) (fun n => n)
    (fun p n f => shapeFace f) (fun n => eq_refl)
    (fun p m n f g => eq_sym (shapeFaceComp f g)).

Definition semiShapeOpInclusion: Functor (Op (νSemiShape A)) (Op (νShape A)) :=
  opFunctor semiShapeInclusion.

Definition shapeCoface n q (a: A): Shape A n (S n) := shapeFace (wgen n q a).
Definition shapeCodegeneracy n q: Shape A (S n) n := shapeMask (wgen (A := hunit) n q tt).

Lemma shapeCofaceTop n (a: A): shapeCoface n n a = shapeConst a (shapeId n).
Proof. unfold shapeCoface. rewrite wgenTop. reflexivity. Qed.

Lemma shapeCodegeneracyTop n: shapeCodegeneracy n n = shapeDrop (shapeId n).
Proof. unfold shapeCodegeneracy. rewrite wgenTop. reflexivity. Qed.

Lemma shapeCofaceLift {n q} (Hq: q <= n) (a: A):
  shapeCoface (S n) q a = shapeKeep (shapeCoface n q a).
Proof. unfold shapeCoface. rewrite (wgenLift Hq). reflexivity. Qed.

Lemma shapeCodegeneracyLift {n q} (Hq: q <= n):
  shapeCodegeneracy (S n) q = shapeKeep (shapeCodegeneracy n q).
Proof. unfold shapeCodegeneracy. rewrite (wgenLift Hq). reflexivity. Qed.

Lemma shapeFaceDgnId (n: nat): forall q (Hq: q <= n) (a: A),
  shapeComp (shapeCoface n q a) (shapeCodegeneracy n q) = shapeId n.
Proof.
  induction n as [|n IH]; intros q Hq a.
  - pose proof (leR0Eq Hq); subst q. reflexivity.
  - destruct (Nat.eqb q (S n)) eqn:E.
    + pose proof (natEqbEq _ _ E); subst q.
      rewrite shapeCofaceTop, shapeCodegeneracyTop, shapeCompConstDrop, shapeIdL. reflexivity.
    + pose proof (leRDown q n Hq E) as Hq'.
      rewrite (shapeCofaceLift Hq'), (shapeCodegeneracyLift Hq'), shapeCompKeep, (IH q Hq').
      reflexivity.
Qed.

Lemma shapeFaceDgnInf (n: nat): forall r q (Hr: r <= q) (Hq: q <= n) (a: A),
  shapeComp (shapeCoface (S n) r a) (shapeCodegeneracy (S n) (S q))
  = shapeComp (shapeCodegeneracy n q) (shapeCoface n r a).
Proof.
  induction n as [|n IH]; intros r q Hr Hq a.
  - pose proof (leR0Eq Hq); subst q. pose proof (leR0Eq Hr); subst r. reflexivity.
  - destruct (Nat.eqb q (S n)) eqn:E.
    + pose proof (natEqbEq _ _ E); subst q.
      rewrite (shapeCofaceLift Hr), !shapeCodegeneracyTop.
      rewrite shapeCompKeepDrop, shapeCompDrop, shapeIdL, shapeIdR. reflexivity.
    + pose proof (leRDown q n Hq E) as Hq'.
      rewrite (shapeCodegeneracyLift Hq'), (shapeCofaceLift (Hr ↕ Hq')).
      rewrite (shapeCofaceLift (↑ (Hr ↕ Hq'))), (shapeCodegeneracyLift (⇑ Hq')).
      rewrite !shapeCompKeep, (IH r q Hr Hq'). reflexivity.
Qed.

Lemma shapeFaceDgnSup (n: nat): forall q (Hq: q <= n) r (Hr: r <= q) (a: A),
  shapeComp (shapeCoface (S n) (S q) a) (shapeCodegeneracy (S n) r)
  = shapeComp (shapeCodegeneracy n r) (shapeCoface n q a).
Proof.
  induction n as [|n IH]; intros q Hq r Hr a.
  - pose proof (leR0Eq Hq); subst q. pose proof (leR0Eq Hr); subst r. reflexivity.
  - destruct (Nat.eqb q (S n)) eqn:E.
    + pose proof (natEqbEq _ _ E); subst q.
      rewrite !shapeCofaceTop, (shapeCodegeneracyLift Hr).
      rewrite shapeCompConstKeep, shapeCompConst, shapeIdL, shapeIdR. reflexivity.
    + pose proof (leRDown q n Hq E) as Hq'.
      rewrite (shapeCodegeneracyLift (Hr ↕ Hq')), (shapeCofaceLift Hq').
      rewrite (shapeCofaceLift (⇑ Hq')), (shapeCodegeneracyLift (↑ (Hr ↕ Hq'))).
      rewrite !shapeCompKeep, (IH q Hq' r Hr). reflexivity.
Qed.

Lemma shapeDgnDgn n r q (Hr: r <= q) (Hq: q <= n):
  shapeComp (shapeCodegeneracy (S n) r) (shapeCodegeneracy n q)
  = shapeComp (shapeCodegeneracy (S n) (S q)) (shapeCodegeneracy n r).
Proof.
  unfold shapeCodegeneracy. rewrite !shapeMaskComp.
  rewrite (wgenExchange (A := hunit) n q Hq r Hr tt tt). reflexivity.
Qed.

Definition shapeShift: Functor (Op (νShape A)) (Op (νShape A)) :=
  Build_Functor (Op (νShape A)) (Op (νShape A)) S
    (fun p n f => shapeKeep f) (fun n => eq_refl)
    (fun p m n f g => eq_sym (shapeCompKeep g f)).

Lemma shapeMaskSkip {p k} (d: Word hunit k p):
  shapeMask (A := A) (wskip (A := hunit) tt d)
  = shapeComp (shapeCodegeneracy p p) (shapeMask d).
Proof. rewrite shapeCodegeneracyTop, shapeCompDrop, shapeIdL. reflexivity. Qed.

End Generators.
