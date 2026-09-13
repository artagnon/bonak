(** Degeneracy layers over the νSet constructed from a presheaf. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet LeSProp NatLemmas Notation νSet.Layer
  Equiv.Dgn.PresheafOfνDgnSet Limit.
From Bonak.Lib Require Import Equiv.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module νDgnSetOfPresheaf (A: LayerSig).
Import A.
Module Export Backward := Bonak.Equiv.Dgn.PresheafOfνDgnSet.PresheafOfνDgnSet A.

Section Forward.
Variable psh: PshEq.Psh.Presheaf.
Variable dgn: PresheafDgn psh.

Definition pshTotal (n: nat): HSet := νTotal (pshFrom psh n).

Definition pshTotalEquiv (n: nat): Equiv (pshTotal n) (psh.(F0) n) :=
  match n with
  | 0 => fillerEquiv
      (B := mkFrame (toDepsRestr ((νSetAt 0).(data) tt).(restrFrames)))
      (fun _: psh.(F0) 0 => tt)
  | n.+1 => fillerEquiv (mkPshFrame psh (towerPshDeps psh (pshTw psh n)))
  end.

Definition pshCell n: pshTotal n -> psh.(F0) n := pshTotalEquiv n.

Lemma pshCellInj n (x y: pshTotal n): pshCell n x = pshCell n y -> x = y.
Proof.
  exact (eqvInj (pshTotalEquiv n)).
Qed.

Definition pshFace n i (Hi: i <= n) (ε: arity):
  pshTotal n.+1 -> pshTotal n :=
  νFaceFuel (pshFrom psh n) (n - i) ε.

Lemma pshCellFace n i (Hi: i <= n) (ε: arity) (x: pshTotal n.+1):
  pshCell n (pshFace n i Hi ε x) =
  psh.(Face) n i Hi ε (pshCell n.+1 x).
Proof.
  destruct n.
  - exact (gfFaceBottom0 psh i Hi ε x).
  - exact (gfFaceBottom psh n i Hi ε x).
Qed.

Definition pshRevFace n q (Hq: q <= n) (ε: arity):
  psh.(F0) n.+1 -> psh.(F0) n :=
  psh.(Face) n (n - q) (sub_leR n q) ε.

Definition pshRevDgn n i (Hi: i <= n): psh.(F0) n -> psh.(F0) n.+1 :=
  dgn.(Dgn _) n (n - i) (sub_leR n i).

Lemma pshCellFaceDown n q (Hq: q <= n) (ε: arity) (x: pshTotal n.+1):
  pshCell n (faceDown (νDepsCohs2At (pshFrom psh n)) q ε x.1) =
  pshRevFace n q Hq ε (pshCell n.+1 x).
Proof.
  pose proof (pshCellFace n (n - q) (sub_leR n q) ε x) as e.
  unfold pshFace in e. rewrite (subSubCancel Hq) in e. exact e.
Qed.

Lemma pshRevFaceDgnId n i (Hi: i <= n) (ε: arity) (x: psh.(F0) n):
  pshRevFace n i Hi ε (pshRevDgn n i Hi x) = x.
Proof.
  exact (dgn.(FaceDgnId _) n (n - i) (sub_leR n i) ε x).
Qed.

Lemma pshRevFaceDgnSup n q i (Hq: q <= i) (Hi: i <= n)
  (ε: arity) (x: psh.(F0) n.+1):
  pshRevFace n.+1 q (Hq ↕ (↑ Hi)) ε (pshRevDgn n.+1 i.+1 (⇑ Hi) x) =
  pshRevDgn n i Hi (pshRevFace n q (Hq ↕ Hi) ε x).
Proof.
  unfold pshRevFace, pshRevDgn.
  generalize (sub_leR n.+1 q).
  rewrite (subSuccL (Hq ↕ Hi)). intro H.
  exact (dgn.(FaceDgnSup _) n (n - q) (sub_leR n q)
    (n - i) (subAntitone Hq) ε x).
Qed.

Lemma pshRevFaceDgnInf n q i (Hi: i <= q) (Hq: q <= n)
  (ε: arity) (x: psh.(F0) n.+1):
  pshRevFace n.+1 q.+1 (⇑ Hq) ε (pshRevDgn n.+1 i (Hi ↕ (↑ Hq)) x) =
  pshRevDgn n i (Hi ↕ Hq) (pshRevFace n q Hq ε x).
Proof.
  unfold pshRevFace, pshRevDgn.
  generalize (sub_leR n.+1 i).
  rewrite (subSuccL (Hi ↕ Hq)). intro H.
  exact (dgn.(FaceDgnInf _) n (n - q) (n - i)
    (subAntitone Hi) (sub_leR n i) ε x).
Qed.

Lemma pshRevDgnDgn n q r (Hq: q <= r) (Hr: r <= n) (x: psh.(F0) n):
  pshRevDgn n.+1 r.+1 (⇑ Hr) (pshRevDgn n q (Hq ↕ Hr) x) =
  pshRevDgn n.+1 q (Hq ↕ (↑ Hr)) (pshRevDgn n r Hr x).
Proof.
  unfold pshRevDgn.
  generalize (sub_leR n.+1 q).
  rewrite (subSuccL (Hq ↕ Hr)). intro H.
  exact (dgn.(DgnDgn _) n (n - r) (n - q)
    (subAntitone Hq) (sub_leR n q) x).
Qed.

Definition PshDgnPrefix (n: nat): Type :=
  (νDgnSetAt n.+1).(dgnPrefix) (pshApprox psh n.+1).

Definition pshDgnData n (R: PshDgnPrefix n):
  DgnData (νDataAt (pshApprox psh n)) (this (pshFrom psh n)) :=
  (νDgnSetAt n).(dgnStepData) (pshApprox psh n) R.1
    (this (pshFrom psh n)) R.2.

Definition pshDgnDeps n (R: PshDgnPrefix n): DepsReflCohsSup n 0 :=
  dgnDepsReflCohsSupFromData _ _ (this (pshFrom psh n.+1)) (pshDgnData n R).

Definition pshDgnDeps2 n (R: PshDgnPrefix n.+1): DepsReflCohs2 n 0 :=
  dgnDepsReflCohs2FromData _ _ _ (this (pshFrom psh n.+2))
    (pshDgnData n R.1) R.2.1 R.2.2.

Definition pshAbove n (R: PshDgnPrefix n.+1) i (Hi: i <= n)
  (x: pshTotal n): pshTotal n.+1 :=
  (mkReflFrameAbove (pshDgnDeps n R.1) i Hi x.1 x.2; R.2.1 i Hi x.1 x.2).

Fixpoint PshDgnGood n: PshDgnPrefix n -> Type :=
  match n with
  | 0 => fun _ => unit
  | n.+1 => fun R =>
      {_: PshDgnGood n R.1 &T
        forall i (Hi: i <= n) (x: pshTotal n),
        pshCell n.+1 (pshAbove n R i Hi x) =
        pshRevDgn n i Hi (pshCell n x)}
  end.

Lemma pshAboveBoundary n (R: PshDgnPrefix n) (G: PshDgnGood n R)
  i (Hi: i <= n) q (Hq: q <= n) (ε: arity) (x: pshTotal n):
  pshCell n (faceDown (νDepsCohs2At (pshFrom psh n)) q ε
    (mkReflFrameAbove (pshDgnDeps n R) i Hi x.1 x.2)) =
  pshRevFace n q Hq ε (pshRevDgn n i Hi (pshCell n x)).
Proof.
  destruct (natOrder q i) as [H|e|H].
  - destruct i; [now destruct (leR_O_contra H) |].
    destruct n; [now destruct (leR_O_contra Hi) |].
    change (νDepsCohs2At (pshFrom psh n.+1)) with
      (Cohs2OfReflCohsSup (mkDepsReflCohsSup (pshDgnDeps2 n R))).
    change (pshDgnDeps n.+1 R) with (mkDepsReflCohsSup (pshDgnDeps2 n R)).
    rewrite (faceDownAboveSup (pshDgnDeps2 n R) q i H Hi).
    cbv zeta.
    match goal with |- _ = ?rhs =>
      change (pshCell n.+1 (pshAbove n R i Hi
        (faceDown (νDepsCohs2At (pshFrom psh n)) q ε x.1)) = rhs)
    end.
    rewrite G.2, (pshCellFaceDown n q (H ↕ Hi)).
    symmetry. exact (pshRevFaceDgnSup n q i H Hi ε (pshCell n.+1 x)).
  - destruct e.
    rewrite (faceDownAboveId (pshDgnDeps n R) q Hq ε x.1 x.2).
    symmetry. apply pshRevFaceDgnId.
  - destruct q; [now destruct (leR_O_contra H) |].
    destruct n; [now destruct (leR_O_contra Hq) |].
    change (νDepsCohs2At (pshFrom psh n.+1)) with
      (Cohs2OfReflCohsSup (mkDepsReflCohsSup (pshDgnDeps2 n R))).
    change (pshDgnDeps n.+1 R) with (mkDepsReflCohsSup (pshDgnDeps2 n R)).
    rewrite (faceDownAboveInf (pshDgnDeps2 n R) q i H Hq).
    cbv zeta.
    match goal with |- _ = ?rhs =>
      change (pshCell n.+1 (pshAbove n R i (H ↕ Hq)
        (faceDown (νDepsCohs2At (pshFrom psh n)) q ε x.1)) = rhs)
    end.
    rewrite G.2, (pshCellFaceDown n q Hq).
    symmetry. exact (pshRevFaceDgnInf n q i H Hq ε (pshCell n.+1 x)).
Qed.

Lemma pshAboveFrame n (R: PshDgnPrefix n) (G: PshDgnGood n R)
  i (Hi: i <= n) (x: pshTotal n):
  mkReflFrameAbove (pshDgnDeps n R) i Hi x.1 x.2 =
  mkPshFrame psh (towerPshDeps psh (pshTw psh n))
    (pshRevDgn n i Hi (pshCell n x)).
Proof.
  apply (faceDownEq (νDepsCohs2At (pshFrom psh n))). intros q Hq ε.
  apply pshCellInj.
  rewrite (pshAboveBoundary n R G i Hi q Hq ε x).
  symmetry.
  exact (pshCellFaceDown n q Hq ε
    (invEq (pshTotalEquiv n.+1) (pshRevDgn n i Hi (pshCell n x)))).
Qed.

Definition pshDgnLayer n (R: PshDgnPrefix n) (G: PshDgnGood n R):
  dgnHasReflFromData _ _ (this (pshFrom psh n.+1)) (pshDgnData n R) :=
  fun i Hi d c =>
    (pshRevDgn n i Hi (pshCell n (d; c)); pshAboveFrame n R G i Hi (d; c)).

Lemma totalSndEq {B: HSet} {P: B -> Type} {x y: B} {u: P x} {v: P y}
  (e: x = y) (h: ((x; u): {b: B &T P b}) = (y; v)):
  rew [P] e in u = v.
Proof.
  pose proof (projT2_eq h) as H.
  now rewrite (B.(UIP) (h := projT1_eq h) (g := e)) in H.
Qed.

Definition pshDgnLayerCohTop n (R: PshDgnPrefix n.+1) (G: PshDgnGood n.+1 R):
  cohReflAboveAboveL (pshDgnDeps2 n R) (pshDgnLayer n.+1 R G).
Proof.
  intros q r Hq Hr d c.
  apply (totalSndEq (B := νFrame (pshApprox psh n.+2))
    (P := fun D => (this (pshFrom psh n.+2)) D)).
  apply (pshCellInj n.+2).
  change
    (pshRevDgn n.+1 r.+1 (⇑ Hr)
      (pshCell n.+1 (pshAbove n R q (Hq ↕ Hr) (d; c))) =
     pshRevDgn n.+1 q (Hq ↕ (↑ Hr))
      (pshCell n.+1 (pshAbove n R r Hr (d; c)))).
  rewrite !G.2. apply pshRevDgnDgn.
Defined.

Definition pshDgnLayerCoh n (R: PshDgnPrefix n) (G: PshDgnGood n R):
  dgnCohLFromData _ _ (this (pshFrom psh n.+1)) (pshDgnData n R)
    (pshDgnLayer n R G).
Proof.
  destruct n.
  - exact tt.
  - exact (mkCohReflAboveAbovePaintings (pshDgnDeps2 n R)
      (TopReflCoh2Dep (deps := pshDgnDeps2 n R)
        (pshDgnLayer n.+1 R G) (pshDgnLayerCohTop n R G))).
Defined.

Definition pshDgnPrefixStep n (R: PshDgnPrefix n) (G: PshDgnGood n R):
  PshDgnPrefix n.+1 := (R; (pshDgnLayer n R G; pshDgnLayerCoh n R G)).

Definition pshDgnGoodStep n (R: PshDgnPrefix n) (G: PshDgnGood n R):
  PshDgnGood n.+1 (pshDgnPrefixStep n R G) :=
  (G; fun i Hi x => eq_refl).

Fixpoint pshDgnChain n: {R: PshDgnPrefix n &T PshDgnGood n R} :=
  match n with
  | 0 => ((tt; tt); tt)
  | n.+1 =>
      let s := pshDgnChain n in
      (pshDgnPrefixStep n s.1 s.2; pshDgnGoodStep n s.1 s.2)
  end.

Definition pshDgnApprox n: DgnPrefix n :=
  (pshApprox psh n;
   match n return (νDgnSetAt n).(dgnPrefix) (pshApprox psh n) with
   | 0 => tt
   | n.+1 => (pshDgnChain n).1
   end).

Definition pshDgnFrom m: νDgnSetsFrom m (pshDgnApprox m) :=
  ofChain (T := dgnTel) pshDgnApprox (fun n =>
    match n with 0 => eq_refl | n.+1 => eq_refl end) m.

Definition f: νDgnSets := pshDgnFrom 0.

Definition pshDgnPosition n: DgnPosition n := (pshDgnApprox n; pshDgnFrom n).

Definition pshDgnPositionNext n:
  dgnPositionNext n (pshDgnPosition n) = pshDgnPosition n.+1.
Proof.
  destruct n; reflexivity.
Defined.

Fixpoint pshDgnPack n:
  νDgnPack n f = pshDgnPosition n :=
  match n with
  | 0 => eq_refl
  | n.+1 => f_equal (dgnPositionNext n) (pshDgnPack n) • pshDgnPositionNext n
  end.

End Forward.
End νDgnSetOfPresheaf.

Module νDgnSetOfPresheafSimplicial := νDgnSetOfPresheaf SimplicialLayer.
Module νDgnSetOfPresheafCubical := νDgnSetOfPresheaf CubicalLayer.
