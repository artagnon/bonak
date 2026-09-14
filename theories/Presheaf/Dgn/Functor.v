(** Interpreting ν-shape morphisms in face presentations with degeneracies.
    A normal form acts by its face word followed by its selection mask. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Notation LeSProp.
From Bonak.Category Require Import Category HSetCat.
From Bonak.Presheaf Require Import WordAction Functor.
From Bonak.Presheaf.Dgn Require Export Generators MaskAction.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Printing Projections.

Section DgnFunctor.
Context {A: HSet}.

Definition applyShape {p n} {P: νSetPresentation A} (R: νDgnStructure P)
  (s: Shape A p n) (x: P.(F0) n): P.(F0) p :=
  applyMask (fst s.2) R (applyW n (snd s.2) (pshStr P) x).

Lemma applyShapeConst {p n} {P: νSetPresentation A} (R: νDgnStructure P)
  (s: Shape A p n) (a: A) x:
  applyShape R (shapeConst a s) x = applyShape R s (P.(Face) n n leR_refl a x).
Proof. reflexivity. Qed.

Lemma applyShapeDrop {p n} {P: νSetPresentation A} (R: νDgnStructure P)
  (s: Shape A p n) x:
  applyShape R (shapeDrop s) x = topDgn R p (applyShape R s x).
Proof. reflexivity. Qed.

Lemma applyShapeKeep {p n} {P: νSetPresentation A} (R: νDgnStructure P)
  (s: Shape A p n) x:
  applyShape R (shapeKeep s) x = applyShape (shiftDgn R) s x.
Proof. reflexivity. Qed.

Lemma applyWTopDgn {m k} (f: Word A k m) {P: νSetPresentation A} (R: νDgnStructure P) x:
  applyW m f (pshStr (shiftPresheaf P)) (topDgn R m x)
  = topDgn R k (applyW m f (pshStr P) x).
Proof.
  exact (applyWMap m k f (pshStr P) (pshStr (shiftPresheaf P)) (topDgn R)
    (fun n q Hq a x => R.(FaceDgnInf _) n q n Hq leR_refl a x) x).
Qed.

Lemma crossAction (m: nat): forall k l (f: Word A k m) (d: Word hunit l m)
  (P: νSetPresentation A) (R: νDgnStructure P) x,
  applyW m f (pshStr P) (applyMask d R x) = applyShape R (cross f d) x.
Proof.
  induction m as [|m IH]; intros k l f d P R x.
  - destruct k as [|k], l as [|l]; try destruct f; try destruct d. reflexivity.
  - destruct f as [[a f]|f], d as [[[] d]|d].
    + cbn [applyW applyMask cross]. unfold sTop; cbn [pshStr SFace].
      rewrite R.(FaceDgnId _). exact (IH k l f d P R x).
    + destruct l as [|l]; [destruct d|].
      cbn [applyW applyMask cross]. rewrite applyShapeConst.
      unfold sTop; cbn [pshStr SFace].
      rewrite applyMaskTopFace. exact (IH k l f d P R _).
    + destruct k as [|k]; [destruct f|].
      cbn [applyW applyMask cross]. rewrite applyShapeDrop.
      change (applyW m f (pshStr (shiftPresheaf P)) (topDgn R m (applyMask d R x))
        = topDgn R k (applyShape R (cross f d) x)).
      rewrite applyWTopDgn. exact (f_equal (topDgn R k) (IH k l f d P R x)).
    + destruct k as [|k], l as [|l]; try destruct f; try destruct d.
      cbn [applyW applyMask cross]. rewrite applyShapeKeep.
      exact (IH k l f d (shiftPresheaf P) (shiftDgn R) x).
Qed.

Lemma applyShapeId {P: νSetPresentation A} (R: νDgnStructure P) n x:
  applyShape R (shapeId n) x = x.
Proof.
  unfold applyShape, shapeId; cbn.
  rewrite applyW_id. apply applyMaskId.
Qed.

Lemma applyShapeComp {p m n} (f: Shape A p m) (g: Shape A m n)
  {P: νSetPresentation A} (R: νDgnStructure P) x:
  applyShape R (shapeComp f g) x = applyShape R f (applyShape R g x).
Proof.
  destruct f as [i [r f]], g as [j [s g]].
  unfold shapeComp, applyShape; cbn.
  rewrite crossAction.
  destruct (cross f s) as [k [u v]]. unfold applyShape, shapeSandwich; cbn.
  rewrite <- (applyWComp n j k g v (pshStr P) P.(FaceCoh) x).
  rewrite applyMaskComp. reflexivity.
Qed.

Definition toDgnFunctor (P: νDgnSetPresentation A): Functor (Op (νShape A)) HSetCat.
Proof.
  refine (Build_Functor (Op (νShape A)) HSetCat P.1.(F0)
    (fun a b s => applyShape P.2 s) _ _).
  - intro n. apply functional_extensionality_dep; intro x. apply applyShapeId.
  - intros a b c f g. apply functional_extensionality_dep; intro x. apply applyShapeComp.
Defined.

(** Restrict a functor to the generating cofaces and coordinate deletions. *)

Definition ofDgnUnderlying (F: Functor (Op (νShape A)) HSetCat): νSetPresentation A :=
  ofFunctor A (semiShapeOpInclusion ⨟ᶠ F).

Definition ofDgnStructure (F: Functor (Op (νShape A)) HSetCat):
  νDgnStructure (ofDgnUnderlying F).
Proof.
  refine (Build_νDgnStructure (ofDgnUnderlying F)
    (fun n q Hq => F.(fhom) (shapeCodegeneracy n q)) _ _ _ _).
  - intros n r q Hr Hq a x.
    change (F.(fhom) (shapeCoface (S n) r a) (F.(fhom) (shapeCodegeneracy (S n) (S q)) x)
      = F.(fhom) (shapeCodegeneracy n q) (F.(fhom) (shapeCoface n r a) x)).
    rewrite !fhomCompPt. change (F.(fhom) (shapeComp (shapeCoface (S n) r a) (shapeCodegeneracy (S n) (S q))) x
      = F.(fhom) (shapeComp (shapeCodegeneracy n q) (shapeCoface n r a)) x).
    rewrite (shapeFaceDgnInf n r q Hr Hq a). reflexivity.
  - intros n q Hq a x.
    change (F.(fhom) (shapeCoface n q a) (F.(fhom) (shapeCodegeneracy n q) x) = x).
    rewrite fhomCompPt. change (F.(fhom) (shapeComp (shapeCoface n q a) (shapeCodegeneracy n q)) x = x).
    rewrite (shapeFaceDgnId n q Hq a). exact (fhomIdPt F n x).
  - intros n q Hq r Hr a x.
    change (F.(fhom) (shapeCoface (S n) (S q) a) (F.(fhom) (shapeCodegeneracy (S n) r) x)
      = F.(fhom) (shapeCodegeneracy n r) (F.(fhom) (shapeCoface n q a) x)).
    rewrite !fhomCompPt. change (F.(fhom) (shapeComp (shapeCoface (S n) (S q) a) (shapeCodegeneracy (S n) r)) x
      = F.(fhom) (shapeComp (shapeCodegeneracy n r) (shapeCoface n q a)) x).
    rewrite (shapeFaceDgnSup n q Hq r Hr a). reflexivity.
  - intros n r q Hr Hq x.
    change (F.(fhom) (shapeCodegeneracy (S n) r) (F.(fhom) (shapeCodegeneracy n q) x)
      = F.(fhom) (shapeCodegeneracy (S n) (S q)) (F.(fhom) (shapeCodegeneracy n r) x)).
    rewrite !fhomCompPt. change (F.(fhom) (shapeComp (shapeCodegeneracy (S n) r) (shapeCodegeneracy n q)) x
      = F.(fhom) (shapeComp (shapeCodegeneracy (S n) (S q)) (shapeCodegeneracy n r)) x).
    rewrite (shapeDgnDgn n r q Hr Hq). reflexivity.
Defined.

Definition ofDgnFunctor (F: Functor (Op (νShape A)) HSetCat): νDgnSetPresentation A :=
  (ofDgnUnderlying F; ofDgnStructure F).

End DgnFunctor.
