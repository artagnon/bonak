(** Face presentations with degeneracies are presheaves on ν-shape. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Equiv Univalence.
From Bonak.Category Require Import Category HSetCat.
Require Export Bonak.Presheaf.Dgn.Roundtrip.

Definition pshDgnEquivFunctor (A: HSet):
  Equiv (νDgnSetPresentation A) (Functor (Op (νShape A)) HSetCat) :=
  qinvEquiv toDgnFunctor ofDgnFunctor ofToDgnFunctor toOfDgnFunctor.

Definition pshDgnEqFunctor (A: HSet):
  νDgnSetPresentation A = Functor (Op (νShape A)) HSetCat :=
  ua (pshDgnEquivFunctor A).
