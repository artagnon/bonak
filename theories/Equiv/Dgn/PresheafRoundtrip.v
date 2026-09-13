(** Recovering a presheaf with degeneracies from its indexed construction. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet LeSProp NatLemmas Notation νSet.Layer
  Equiv.Dgn.νDgnSetOfPresheaf Limit.
From Bonak.Lib Require Import Equiv.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module PresheafRoundtrip (A: LayerSig).
Import A.
Module Export Forward := Bonak.Equiv.Dgn.νDgnSetOfPresheaf.νDgnSetOfPresheaf A.

Definition positionEquiv n {s t: DgnPosition n} (e: s = t):
  Equiv (dgnPositionTotal n s) (dgnPositionTotal n t).
Proof.
  destruct e. exact idEquiv.
Defined.

Section Roundtrip.
Variable psh: PshEq.Psh.Presheaf.
Variable dgn: PresheafDgn psh.

Definition candidateEquiv n:
  Equiv (dgnPositionTotal n (pshDgnPosition psh dgn n)) (psh.(F0) n).
Proof.
  destruct n.
  - exact (pshTotalEquiv psh 0).
  - exact (pshTotalEquiv psh n.+1).
Defined.

Lemma gfFaceAt n (s: DgnPosition n) (e: s = pshDgnPosition psh dgn n)
  i (Hi: i <= n) (ε: arity)
  (x: dgnPositionTotal n.+1 (dgnPositionNext n s)):
  candidateEquiv n (positionEquiv n e (dgnPositionFace n s i Hi ε x)) =
  psh.(Face) n i Hi ε
    (candidateEquiv n.+1 (positionEquiv n.+1
      (f_equal (dgnPositionNext n) e • pshDgnPositionNext psh dgn n) x)).
Proof.
  subst s. destruct n.
  - exact (pshCellFace psh 0 i Hi ε x).
  - exact (pshCellFace psh n.+1 i Hi ε x).
Qed.

Lemma gfDgnAt n (s: DgnPosition n) (e: s = pshDgnPosition psh dgn n)
  i (Hi: i <= n) (x: dgnPositionTotal n s):
  candidateEquiv n.+1 (positionEquiv n.+1
    (f_equal (dgnPositionNext n) e • pshDgnPositionNext psh dgn n)
    (dgnPositionMap n s i Hi x)) =
  dgn.(Dgn _) n i Hi (candidateEquiv n (positionEquiv n e x)).
Proof.
  subst s. destruct n.
  - destruct i; [reflexivity | now destruct (leR_O_contra Hi)].
  - change (pshRevDgn psh dgn n.+1 (n.+1 - i) (sub_leR n.+1 i)
      (pshCell psh n.+1 x) = dgn.(Dgn _) n.+1 i Hi (pshCell psh n.+1 x)).
    unfold pshRevDgn.
    generalize (sub_leR n.+1 (n.+1 - i)).
    rewrite (subSubCancel Hi). intro H. reflexivity.
Qed.

Definition gfF0 n:
  Equiv ((g (f psh dgn)).1.(F0) n) (psh.(F0) n) :=
  compEquiv (positionEquiv n (pshDgnPack psh dgn n)) (candidateEquiv n).

Lemma gfFace n i (Hi: i <= n) (ε: arity)
  (x: (g (f psh dgn)).1.(F0) n.+1):
  gfF0 n ((g (f psh dgn)).1.(Face) n i Hi ε x) =
  psh.(Face) n i Hi ε (gfF0 n.+1 x).
Proof.
  exact (gfFaceAt n (νDgnPack n (f psh dgn))
    (pshDgnPack psh dgn n) i Hi ε x).
Qed.

Lemma gfDgn n i (Hi: i <= n)
  (x: (g (f psh dgn)).1.(F0) n):
  gfF0 n.+1 ((g (f psh dgn)).2.(Dgn _) n i Hi x) =
  dgn.(Dgn _) n i Hi (gfF0 n x).
Proof.
  exact (gfDgnAt n (νDgnPack n (f psh dgn))
    (pshDgnPack psh dgn n) i Hi x).
Qed.

Definition gf: PresheafEquiv (g (f psh dgn)) (psh; dgn) :=
  Build_PresheafEquiv (g (f psh dgn)) (psh; dgn)
    (PshEq.Build_PresheafEquiv _ psh gfF0 gfFace) gfDgn.

Definition gfEq: g (f psh dgn) = (psh; dgn) :=
  presheafEquivEq gf.

End Roundtrip.
End PresheafRoundtrip.

Module PresheafRoundtripSimplicial := PresheafRoundtrip SimplicialLayer.
Module PresheafRoundtripCubical := PresheafRoundtrip CubicalLayer.
