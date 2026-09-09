(** Translations between face presentations and set-valued functors. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation LeSProp.
From Bonak.Category Require Import Category HSetCat CategoryEq.
From Bonak.Presheaf Require Import νSemiShape WordAction.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak.Presheaf Require Export Presentation.

Set Primitive Projections.
Set Printing Projections.

Definition pshStr {A: HSet} (P: Presheaf A): FaceStr A := {|
  S0 n := P.(F0) n;
  SFace := P.(Face);
|}.

Section PresheafFunctor.
Context (A: HSet).

(** Interpreting faces along words *)

Definition toFunctor (P: Presheaf A): Functor (Op (νSemiShape A)) HSetCat :=
  Build_Functor (Op (νSemiShape A)) HSetCat (fun n => P.(F0) n)
    (fun a b w => applyW a w (pshStr P))
    (fun a => functional_extensionality_dep _ _
       (fun x => applyW_id (pshStr P) x))
    (fun a b c f g => functional_extensionality_dep _ _
       (fun x => eq_sym (applyWComp a b c f g (pshStr P) P.(FaceCoh) x))).

(** Restricting a functor to generating cofaces *)

Lemma ofFunctorCoh (F: Functor (Op (νSemiShape A)) HSetCat)
  n q (Hq: q <= n) r (Hr: r <= q) (ε ω: A) (X: F.(fobj) (S (S n))):
  F.(fhom) (wgen n q ε) (F.(fhom) (wgen (S n) r ω) X)
  = F.(fhom) (wgen n r ω) (F.(fhom) (wgen (S n) (S q) ε) X).
Proof.
  refine (eq_sym (f_equal (fun h => h X)
    (F.(fcomp) (a := S (S n)) (b := S n) (c := n)
       (wgen (S n) r ω) (wgen n q ε))) • _).
  refine (f_equal (fun w => F.(fhom) (a := S (S n)) (b := n) w X)
    (wgenExchange n q Hq r Hr ε ω) • _).
  now exact (f_equal (fun h => h X)
    (F.(fcomp) (a := S (S n)) (b := S n) (c := n)
       (wgen (S n) (S q) ε) (wgen n r ω))).
Defined.

Definition ofFunctor (F: Functor (Op (νSemiShape A)) HSetCat): Presheaf A :=
  Build_Presheaf A (fun n => F.(fobj) n)
    (fun n q Hq ε => F.(fhom) (a := S n) (b := n) (wgen n q ε))
    (ofFunctorCoh F).

End PresheafFunctor.
