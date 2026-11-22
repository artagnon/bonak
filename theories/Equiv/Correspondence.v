(** The correspondence theorem

    The top-level result: the two presentations of ν-sets — the fibred one
    ([νSetPresentation]) and the indexed one ([νSets]) — are equivalent, and, upgraded
    by univalence, equal.

    This file is a thin wrapper on top of the two round trips:
    - [gf: PresheafEquiv (g (f psh)) psh] from [PresheafRoundtrip.v],
      turned into an equality by [presheafEquivEq] from [PresheafEquiv.v];
    - [fg: f (g X) = X] from [νSetRoundtrip.v].
    It combines them into an [Equiv] between the type of presheaves and the
    type of νSets. Both round trips assume univalence and functional
    extensionality. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import Logic Univalence Equiv.

From Bonak.νSet Require Import Layer νSet.
From Bonak Require Import Face.
From Bonak.Presheaf Require Import Presentation.
From Bonak.Equiv Require Import PresheafEquiv νSetOfPresheaf PresheafOfνSet νSetRoundtrip PresheafRoundtrip.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module CorrespondenceOn (A: LayerSig) (S: νSetSig A).
Import A.

Module Export PresheafRoundtrip := PresheafRoundtrip.PresheafRoundtripOn A S.

Definition presheafνSetsEquiv: Equiv (νSetPresentation arity) νSets :=
  qinvEquiv f g
    (fun psh => presheafEquivEq (gf psh))
    fg.

Definition presheafEqνSets: νSetPresentation arity = νSets := ua presheafνSetsEquiv.

End CorrespondenceOn.

Module Correspondence (A: LayerSig).
Module Base := νSet.νSet A.
Include CorrespondenceOn A Base.
End Correspondence.

Module CorrespondenceSimplicial := Correspondence SimplicialLayer.
Module CorrespondenceCubical := Correspondence CubicalLayer.
