(** The normal-form action and restriction to generators are inverse. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Notation LeSProp Funext.
From Bonak.Category Require Import Category CategoryEq HSetCat.
From Bonak.Presheaf Require Import WordAction Roundtrip.
Require Export Bonak.Presheaf.Dgn.Functor.
From Stdlib Require Import Logic.FunctionalExtensionality.
Set Primitive Projections.
Set Printing Projections.

Section DgnRoundtrip.
Context {A: HSet}.

Lemma applyShapeFace {p n} {P: νSetPresentation A} (R: νDgnStructure P)
  (f: Word A p n) x:
  applyShape R (shapeFace f) x = applyW n f (pshStr P) x.
Proof. unfold applyShape, shapeFace; cbn. apply applyMaskId. Qed.

Lemma applyShapeMask {p n} {P: νSetPresentation A} (R: νDgnStructure P)
  (d: Word hunit n p) x:
  applyShape R (shapeMask d) x = applyMask d R x.
Proof. unfold applyShape, shapeMask; cbn. now rewrite applyW_id. Qed.

Lemma applyShapeCoface {P: νSetPresentation A} (R: νDgnStructure P) n q Hq a x:
  applyShape R (shapeCoface n q a) x = P.(Face) n q Hq a x.
Proof. unfold shapeCoface. rewrite applyShapeFace. exact (applyWgen A (pshStr P) n q Hq a x). Qed.

Lemma applyShapeCodegeneracy {P: νSetPresentation A} (R: νDgnStructure P) n q Hq x:
  applyShape R (shapeCodegeneracy n q) x = R.(Dgn _) n q Hq x.
Proof. unfold shapeCodegeneracy. rewrite applyShapeMask. apply applyMaskGen. Qed.

Lemma ofToDgnFunctor (P: νDgnSetPresentation A): ofDgnFunctor (toDgnFunctor P) = P.
Proof.
  refine (presheafWithDgnEq (ofDgnFunctor (toDgnFunctor P)) P eq_refl _ _); cbn.
  - apply functional_extensionality_dep; intro n.
    apply functional_extensionality_dep; intro q.
    apply spropFunext; intro Hq.
    apply functional_extensionality_dep; intro a.
    apply functional_extensionality_dep; intro x.
    exact (applyShapeCoface P.2 n q Hq a x).
  - apply functional_extensionality_dep; intro n.
    apply functional_extensionality_dep; intro q.
    apply spropFunext; intro Hq.
    apply functional_extensionality_dep; intro x.
    exact (applyShapeCodegeneracy P.2 n q Hq x).
Qed.

(** Allow arbitrary presentations with the functor's object part, so the
    induction is stable under shifting all levels. *)
Lemma applyMaskFhom (p: nat): forall k (d: Word hunit k p)
  (P: νSetPresentation A) (R: νDgnStructure P)
  (Z: FunctorOn (C := Op (νShape A)) (D := HSetCat) P.(F0))
  (Hgen: forall n q Hq x,
    R.(Dgn _) n q Hq x = (ofFunctorOn Z).(fhom) (shapeCodegeneracy n q) x) x,
  applyMask d R x = (ofFunctorOn Z).(fhom) (shapeMask d) x.
Proof.
  induction p as [|p IH]; intros k d P R Z Hgen x.
  - destruct k as [|k]; [destruct d|destruct d].
    exact (eq_sym (fhomIdPt (ofFunctorOn Z) 0 x)).
  - destruct d as [[[] d]|d].
    + cbn [applyMask]. rewrite (IH k d P R Z Hgen x), Hgen.
      rewrite fhomCompPt.
      change ((ofFunctorOn Z).(fhom) (shapeComp (shapeCodegeneracy p p) (shapeMask d)) x
        = (ofFunctorOn Z).(fhom) (shapeMask (wskip (A := hunit) tt d)) x).
      now rewrite shapeMaskSkip.
    + destruct k as [|k]; [destruct d|].
      exact (IH k d (shiftPresheaf P) (shiftDgn R)
        (toFunctorOn (shapeShift ⨟ᶠ ofFunctorOn Z))
        (fun n q Hq x => Hgen (S n) q (↑ Hq) x
          • f_equal (fun s => (ofFunctorOn Z).(fhom) s x) (shapeCodegeneracyLift Hq)) x).
Qed.

Lemma applyShapeFhom (F: Functor (Op (νShape A)) HSetCat)
  {p n} (s: Shape A p n) x:
  applyShape (ofDgnStructure F) s x = F.(fhom) s x.
Proof.
  destruct s as [k [r f]]. unfold applyShape; cbn.
  rewrite (applyMaskFhom p k r (ofDgnUnderlying F) (ofDgnStructure F)
    (toFunctorOn F) (fun n q Hq x => eq_refl)).
  rewrite (applyWfhom A n k f (semiShapeOpInclusion ⨟ᶠ F)
    (ofDgnUnderlying F).(Face) (fun n q Hq a x => eq_refl)).
  change (F.(fhom) (shapeMask r) (F.(fhom) (shapeFace f) x) = F.(fhom) (k; (r, f)) x).
  rewrite fhomCompPt.
  change (F.(fhom) (shapeComp (shapeMask r) (shapeFace f)) x = F.(fhom) (k; (r, f)) x).
  now rewrite shapeFactor.
Qed.

Lemma toOfDgnFunctor (F: Functor (Op (νShape A)) HSetCat):
  toDgnFunctor (ofDgnFunctor F) = F.
Proof.
  refine (functorEq (toDgnFunctor (ofDgnFunctor F)) F eq_refl _); intros a b s.
  apply functional_extensionality_dep; intro x. exact (applyShapeFhom F s x).
Qed.

(** Restriction along the semi-shape inclusion recovers the face functor. *)
Lemma restrictDgnFunctor (P: νDgnSetPresentation A):
  semiShapeOpInclusion ⨟ᶠ toDgnFunctor P = toFunctor A P.1.
Proof.
  refine (functorEq (semiShapeOpInclusion ⨟ᶠ toDgnFunctor P)
    (toFunctor A P.1) eq_refl _); intros a b f.
  apply functional_extensionality_dep; intro x. exact (applyShapeFace P.2 f x).
Qed.

End DgnRoundtrip.
