(** Face maps on arbitrary type families indexed by dimension, with the
    exchange law. No truncation of the levels is assumed. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation LeSProp.
Set Primitive Projections.
Set Printing Projections.

Section FaceStructure.
Context (A: HSet).

Record FaceStr := {
  S0: nat -> Type;
  SFace n q (Hq: q <= n) (ε: A): S0 (S n) -> S0 n;
}.

Definition shiftStr (Q: FaceStr): FaceStr := {|
  S0 n := Q.(S0) (S n);
  SFace n q Hq ε := Q.(SFace) (S n) q (↑ Hq) ε;
|}.

(** The top face at level [n]: the one deleting dimension [n]. *)

Definition sTop (Q: FaceStr) (n: nat) (ε: A): Q.(S0) (S n) -> Q.(S0) n :=
  Q.(SFace) n n leR_refl ε.

End FaceStructure.

Arguments S0 {_} _ _.
Arguments SFace {_} _ _ _ _ _.
Arguments shiftStr {A} Q.
Arguments sTop {A} Q n ε.

Definition CohOf {A: HSet} (Q: FaceStr A): Type :=
  forall n q (Hq: q <= n) r (Hr: r <= q) (ε ω: A) (X: Q.(S0) (S (S n))),
    Q.(SFace) n q Hq ε (Q.(SFace) (S n) r (Hr ↕ (↑ Hq)) ω X) =
    Q.(SFace) n r (Hr ↕ Hq) ω (Q.(SFace) (S n) (S q) (⇑ Hq) ε X).

Definition cohShift {A: HSet} {Q: FaceStr A} (H: CohOf Q): CohOf (shiftStr Q) :=
  fun n q Hq r Hr ε ω X => H (S n) q (↑ Hq) r Hr ε ω X.

(** Exchanging a face with the top face preserves the index of the other
    face. *)

Definition topCoh {A: HSet} {Q: FaceStr A} (H: CohOf Q):
  forall k q (Hq: q <= k) (ε ω: A) (X: Q.(S0) (S (S k))),
    sTop Q k ε (Q.(SFace) (S k) q (↑ Hq) ω X)
    = Q.(SFace) k q Hq ω (sTop Q (S k) ε X) :=
  fun k q Hq ε ω X => H k k leR_refl q Hq ε ω X.
