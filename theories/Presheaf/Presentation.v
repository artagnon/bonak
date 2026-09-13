(** The *fibred* (†) presentation of ν-sets — presheaves over the
    ν-category: one HSet of cells per dimension, with face maps down to the
    dimension below, subject to the exchange law. Each [F0 n.+1] is a single
    set, fibred over its faces by the maps out of it.

    (†) This presentation is usually called the indexed one. Here fibred/indexed
    are used in the sense of Herbelin and Ramachandra, "A parametricity-based
    formalization of semi-simplicial and semi-cubical sets". *)

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet Notation LeSProp.

From Bonak.Lib Require Import Funext.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import Logic.EqNotations.

Set Primitive Projections.
Set Printing Projections.

(** [Face n q Hq ε] removes position [q] with label [ε]. In [FaceCoh],
    deleting [r] first shifts the higher position [q.+1] to [q]; deleting
    [q.+1] first leaves [r] unchanged. *)

Record νSetPresentation (arity: HSet) := {
  F0: nat -> HSet;
  Face n q (Hq: q <= n) (ε: arity): F0 n.+1 -> F0 n;
  FaceCoh n q (Hq: q <= n) r (Hr: r <= q) (ε ω: arity) (X: F0 n.+2):
    Face n q Hq ε (Face n.+1 r (Hr ↕ (↑ Hq)) ω X) =
    Face n r (Hr ↕ Hq) ω (Face n.+1 q.+1 (⇑ Hq) ε X)
}.

Arguments F0 {arity} _ _.
Arguments Face {arity} _ _ _ _ _.
Arguments FaceCoh {arity} _ _ _ _ _ _ _ _ _.

Record νDgnStructure {arity: HSet} (psh: νSetPresentation arity): Type := {
  Dgn n q (Hq: q <= n): psh.(F0) n -> psh.(F0) n.+1;
  FaceDgnInf n r q (Hr: r <= q) (Hq: q <= n) (ε: arity) (X: psh.(F0) n.+1):
    psh.(Face) n.+1 r (Hr ↕ (↑ Hq)) ε (Dgn n.+1 q.+1 (⇑ Hq) X) =
    Dgn n q Hq (psh.(Face) n r (Hr ↕ Hq) ε X);
  FaceDgnId n q (Hq: q <= n) (ε: arity) (X: psh.(F0) n):
    psh.(Face) n q Hq ε (Dgn n q Hq X) = X;
  FaceDgnSup n q (Hq: q <= n) r (Hr: r <= q) (ε: arity) (X: psh.(F0) n.+1):
    psh.(Face) n.+1 q.+1 (⇑ Hq) ε (Dgn n.+1 r (Hr ↕ (↑ Hq)) X) =
    Dgn n r (Hr ↕ Hq) (psh.(Face) n q Hq ε X);
  DgnDgn n r q (Hr: r <= q) (Hq: q <= n) (X: psh.(F0) n):
    Dgn n.+1 r (Hr ↕ (↑ Hq)) (Dgn n q Hq X) =
    Dgn n.+1 q.+1 (⇑ Hq) (Dgn n r (Hr ↕ Hq) X)
}.

Arguments Build_νDgnStructure {arity} _ _ _ _ _ _.
Arguments Dgn {arity} _ _ _ _ _.
Arguments FaceDgnInf {arity} _ _ _ _ _ _ _ _ _.
Arguments FaceDgnId {arity} _ _ _ _ _ _ _.
Arguments FaceDgnSup {arity} _ _ _ _ _ _ _ _ _.
Arguments DgnDgn {arity} _ _ _ _ _ _ _ _.

Definition νDgnSetPresentation (arity: HSet): Type :=
  { P: νSetPresentation arity &T νDgnStructure P }.

Definition AugmentedSemiSimplicialPresentation := νSetPresentation hunit.
Definition SemiCubicalPresentation := νSetPresentation hbool.

(** The levels and faces determine a presentation: the exchange law is an
    equality in an [HSet], so its proofs agree. *)

Lemma presheafEqIntro {arity: HSet} (psh1 psh2: νSetPresentation arity)
  (e0: psh1.(F0) = psh2.(F0))
  (e1: rew [fun F0: nat -> HSet =>
         forall n q (Hq: q <= n) (ε: arity), F0 n.+1 -> F0 n] e0 in
       psh1.(Face) = psh2.(Face)):
  psh1 = psh2.
Proof.
  destruct psh1 as [F01 Face1 Coh1], psh2 as [F02 Face2 Coh2];
    cbn in e0, e1.
  destruct e0; cbn in e1; destruct e1.
  apply (f_equal (fun C => {| F0 := F01; Face := Face1; FaceCoh := C |})).
  apply functional_extensionality_dep_good; intro n.
  apply functional_extensionality_dep_good; intro q.
  apply spropFunext; intro Hq.
  apply functional_extensionality_dep_good; intro r.
  apply spropFunext; intro Hr.
  apply functional_extensionality_dep_good; intro ε.
  apply functional_extensionality_dep_good; intro ω.
  apply functional_extensionality_dep_good; intro Y.
  now apply (F01 n).(UIP).
Qed.
