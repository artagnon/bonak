(** The indexed and presheaf presentations of sets with degeneracies agree.
    As for νSets, the two constructions preserve the operations, their
    round trips give an equivalence, and univalence gives a type equality. *)

Set Warnings "-notation-overridden".
From Bonak Require Import SigT νSet.Layer Univalence Equiv.Dgn.νDgnSetRoundtrip.
From Bonak.Lib Require Import Equiv.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module Correspondence (A: LayerSig).
Module Export Roundtrip := Bonak.Equiv.Dgn.νDgnSetRoundtrip.νDgnSetRoundtrip A.

Definition νDgnSetsPresheafEquiv:
  Equiv νDgnSets {psh: PshEq.Psh.Presheaf &T PresheafDgn psh} :=
  qinvEquiv g (fun P => f P.1 P.2) fg
    (fun P => gfEq P.1 P.2).

Definition νDgnSetsEqPresheaf:
  νDgnSets = {psh: PshEq.Psh.Presheaf &T PresheafDgn psh} :=
  ua νDgnSetsPresheafEquiv.

End Correspondence.

Module CorrespondenceSimplicial := Correspondence SimplicialLayer.
Module CorrespondenceCubical := Correspondence CubicalLayer.
