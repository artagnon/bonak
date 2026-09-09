(** Both round trips between face presentations and set-valued functors. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation LeSProp.
From Bonak.Category Require Import Category HSetCat CategoryEq.
From Bonak.Presheaf Require Import νSemiShape WordAction.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Lib Require Import Funext.

From Bonak.Presheaf Require Export Functor.

Set Primitive Projections.
Set Printing Projections.

Section PresheafRoundtrip.
Context (A: HSet).

(** The round trip on records *)

Lemma ofToFunctor (P: Presheaf A): ofFunctor A (toFunctor A P) = P.
Proof.
  refine (presheafEqIntro (ofFunctor A (toFunctor A P)) P eq_refl _); simpl.
  apply functional_extensionality_dep; intro n.
  apply functional_extensionality_dep; intro q.
  apply spropFunext; intro Hq.
  apply functional_extensionality_dep; intro ε.
  apply functional_extensionality_dep; intro x.
  now exact (applyWgen A (pshStr P) n q Hq ε x).
Qed.

(** The round trip on functors: a functor is determined by its action on the
    generating cofaces, because every word is a composite of them. *)

Lemma applyWfhom (m: nat): forall n (w: Word A n m)
  (F: Functor (Op (νSemiShape A)) HSetCat)
  (SF: forall k q (Hq: q <= k) (ε: A), F.(fobj) (S k) -> F.(fobj) k)
  (HSF: forall k q (Hq: q <= k) (ε: A) x,
     SF k q Hq ε x = F.(fhom) (a := S k) (b := k) (wgen k q ε) x)
  (x: F.(fobj) m),
  applyW m w (Build_FaceStr A (fun k => F.(fobj) k) SF) x
  = F.(fhom) (a := m) (b := n) w x.
Proof.
  induction m as [|m IHm]; intros n w F SF HSF x.
  - destruct n as [|n]; [|now destruct w].
    destruct w. now exact (eq_sym (f_equal (fun h => h x) (F.(fid) 0))).
  - destruct w as [(ε, w)|w].
    + refine (IHm n w F SF HSF (SF m m leR_refl ε x) • _).
      refine (f_equal (F.(fhom) (a := m) (b := n) w) (HSF m m leR_refl ε x) • _).
      refine (eq_sym (f_equal (fun h => h x)
        (F.(fcomp) (a := S m) (b := m) (c := n) (wgen m m ε) w)) • _).
      now exact (f_equal (fun v => F.(fhom) (a := S m) (b := n) v x)
        (wgenSkip ε w)).
    + destruct n as [|n]; [now destruct w|].
      now exact (IHm n w (compFunctor (νSemiShapeShift A) F)
        (fun k q Hq ε => SF (S k) q (↑ Hq) ε)
        (fun k q Hq ε x => HSF (S k) q (↑ Hq) ε x
           • f_equal (fun v => F.(fhom) (a := S (S k)) (b := S k) v x)
               (wgenLift Hq ε)) x).
Defined.

Lemma toOfFunctor (F: Functor (Op (νSemiShape A)) HSetCat):
  toFunctor A (ofFunctor A F) = F.
Proof.
  refine (functorEq (toFunctor A (ofFunctor A F)) F eq_refl _); simpl; intros a b w.
  apply functional_extensionality_dep; intro x.
  now exact (applyWfhom a b w F
    (fun k q Hq ε => F.(fhom) (a := S k) (b := k) (wgen k q ε))
    (fun k q Hq ε x => eq_refl) x).
Qed.

End PresheafRoundtrip.
