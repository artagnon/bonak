(** The correspondence theorem

    The top-level result: the two presentations of ν-sets — the fibred one
    ([Presheaf]) and the indexed one ([νSets]) — are equivalent, and, upgraded
    by univalence, equal.

    This file is a thin wrapper on top of the two round trips:
    - [gf: PresheafEquiv (g (f psh)) psh] from [PresheafRoundtrip.v]
    - [fg: νSetsEquiv (f (g X)) X] from [νSetRoundtrip.v]
    It combines them into an [Equiv] between the type of presheaves and the
    type of νSets. Each side's notion of sameness is turned into an equality
    by a theorem assuming univalence and functional extensionality:
    [presheafEquivEq] from [PresheafEquiv.v] on the fibred side,
    [νSetsEquivEq] from [Extensionality.v] on the indexed side. *)

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation νSet.Layer Univalence
νSet Face PresheafEquiv νSetOfPresheaf PresheafOfνSet
νSetRoundtrip PresheafRoundtrip Limit.
From Bonak.νSet.Lib Require Import Equiv.
Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module Correspondence (A: LayerSig).
Import A.

Module Export PresheafRoundtrip := PresheafRoundtrip.PresheafRoundtrip A.

(** Extensionality for the ν-set tower

    [νSetsEquiv SA SB] relates [SA] and [SB] level by level: at each level
    an equivalence between their filler fibres over the equality of the
    prefixes reached so far, the levels tied together into a chain of prefix
    relations. All restriction and coherence data at a level is computed
    from the prefix, so transport along that equality supplies its
    compatibility.

    The round trip [fg X] constructs this relation between [f (g X)] and [X].
    [νSetsEquivEq] converts it into equality of the two towers by turning
    each level's relation into a path between the finite prefixes. *)

Definition presheafνSetsEquiv: Equiv Presheaf νSets :=
  qinvEquiv f g
    (fun psh => presheafEquivEq (gf psh))
    (fun X => νSetsEquivEq (fg X)).

Definition presheafEqνSets: Presheaf = νSets := ua presheafνSetsEquiv.

End Correspondence.

Module CorrespondenceSimplicial := Correspondence SimplicialLayer.
Module CorrespondenceCubical := Correspondence CubicalLayer.
