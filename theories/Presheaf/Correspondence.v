(** The equivalence between face presentations and set-valued functors. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet.
From Bonak.Lib Require Import Equiv Univalence.
From Bonak.Category Require Import Category HSetCat CategoryEq.
From Bonak.Presheaf Require Import νSemiShape.
From Bonak.Presheaf Require Export Roundtrip.

Set Primitive Projections.
Set Printing Projections.

Section Correspondence.
Context (A: HSet).

Definition pshEquivFunctor:
  Equiv (Presheaf A) (Functor (Op (νSemiShape A)) HSetCat) :=
  qinvEquiv (toFunctor A) (ofFunctor A) (ofToFunctor A) (toOfFunctor A).

End Correspondence.

(** The set-level correspondence as an equality of types, by univalence. *)

Definition pshEqFunctor (A: HSet):
  Presheaf A = Functor (Op (νSemiShape A)) HSetCat :=
  ua (pshEquivFunctor A).

(** The correspondence at the augmented semi-simplicial and semi-cubical
    arities, as equalities of types. *)

Definition simplicialPresheafEqFunctor:
  AugmentedSemiSimplicialPresheaf = Functor (Op (νSemiShape hunit)) HSetCat :=
  pshEqFunctor hunit.

Definition cubicalPresheafEqFunctor:
  SemiCubicalPresheaf = Functor (Op (νSemiShape hbool)) HSetCat :=
  pshEqFunctor hbool.
