(** The *fibred* (†) presentation of ν-sets — presheaves over the
    ν-category: one HSet of cells per dimension, with face maps down to the
    dimension below, subject to the exchange law. Each [F0 n.+1] is a single
    set, fibred over its faces by the maps out of it.

    (†) This presentation is usually called the indexed one. Here fibred/indexed
    are used in the sense of Herbelin and Ramachandra, "A parametricity-based
    formalization of semi-simplicial and semi-cubical sets". *)

Set Warnings "-notation-overridden".
From Bonak Require Import HSet Notation LeSProp νSet.Layer.

Set Primitive Projections.
Set Printing Projections.

Module Presheaf (A: LayerSig).
Import A.

(** [Face n q Hq ε] is the face map removing dimension [q] in direction [ε],
    from level [n.+1] down to level [n]. [FaceCoh] is the exchange law: the
    two ways of erasing dimensions [r] and [q.+1] (for [r <= q]) from a cell
    of level [n.+2] agree. *)

Record Presheaf := {
  F0: nat -> HSet;
  Face n q (Hq: q <= n) (ε: arity): F0 n.+1 -> F0 n;
  FaceCoh n q (Hq: q <= n) r (Hr: r <= q) (ε ω: arity) (X: F0 n.+2):
    Face n q Hq ε (Face n.+1 r (Hr ↕ (↑ Hq)) ω X) =
    Face n r (Hr ↕ Hq) ω (Face n.+1 q.+1 (⇑ Hq) ε X)
}.

End Presheaf.

Module PresheafSimplicial := Presheaf SimplicialLayer.
Module PresheafCubical := Presheaf CubicalLayer.

Definition AugmentedSemiSimplicialPresheaf := PresheafSimplicial.Presheaf.
Definition SemiCubicalPresheaf := PresheafCubical.Presheaf.
