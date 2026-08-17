(** The correspondence theorem

    The top-level result: the two presentations of ν-sets — the fibred one
    ([Presheaf]) and the indexed one ([νSets]) — are equivalent, and, upgraded
    by univalence, equal.

    This file is a thin wrapper on top of the two round trips:
    - [gf: PresheafEquiv (g (f psh)) psh] from [PresheafRoundtrip.v]
    - [fg: νSetFromEquiv trTower0 (f (g X)) X] from [νSetRoundtrip.v]
    It combines them into an actual [Equiv] between the type of presheaves and
    the type of νSets. The axioms enter where each side's notion of sameness is
    turned into an equality — [presheafEquivEq] from [PresheafEquiv.v] on the
    fibred side (a theorem, from univalence and funext), [νSetFromEquivEq] below
    on the indexed side (an axiom, stream extensionality). *)

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation νSet.Layer Univalence
  νSet Face PresheafEquiv νSetOfPresheaf PresheafOfνSet
  νSetRoundtrip PresheafRoundtrip.
From Bonak.νSet.Lib Require Import Equiv.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module Correspondence (A: LayerSig).
Import A.

Module Export PresheafRoundtrip := PresheafRoundtrip.PresheafRoundtrip A.

(** Extensionality for the coinductive ν-set tower

    [νSetFromEquiv trTower0 SA SB] relates [SA] and [SB] level by level. At
    each level it contains equivalences between their filler fibres, proofs
    that these equivalences commute with the stored restriction paintings,
    and a corresponding relation between the tails.

    The round trip [fg X] constructs this relation between [f (g X)] and [X].
    The axiom below converts it into equality of the two coinductive towers.

    Rocq's rules for primitive coinductive records do not provide this
    extensionality principle. The intensional-stream model of Boulier, Pédrot,
    and Tabareau, "The Next 700 Syntactical Models of Type Theory", Theorem 13,
    separates bisimilarity from identity by adding state that identity observes
    and the coinductive projections do not. The translation leaves universes
    unchanged, so the separation is compatible with an assumed univalence
    axiom. *)

Axiom νSetFromEquivEq: forall SA SB: νSets,
  νSetFromEquiv trTower0 SA SB -> SA = SB.

Definition presheafνSetsEquiv: Equiv Presheaf νSets :=
  qinvEquiv f g
    (fun psh => presheafEquivEq (gf psh))
    (fun X => νSetFromEquivEq (f (g X)) X (fg X)).

Definition presheafEqνSets: Presheaf = νSets := ua presheafνSetsEquiv.

End Correspondence.

Module CorrespondenceSimplicial := Correspondence SimplicialLayer.
Module CorrespondenceCubical := Correspondence CubicalLayer.
