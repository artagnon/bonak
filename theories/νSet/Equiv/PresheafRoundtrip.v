(** The forward round trip [g ∘ f] of the correspondence between the
    fibred presentation ([Presheaf]) and the indexed construction
    ([νSet]): [gf: PresheafEquiv (g (f psh)) psh]. Levelwise, projecting a
    candidate-filled cell to its [psh]-cell is an equivalence, and it
    commutes with the face maps by [pshνFace]. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.Eqdep_dec Arith.Peano_dec.
From Bonak Require Import SigT RewLemmas HSet LeSProp NatLemmas Notation νSet.Layer
  νSet Face Presheaf νSetOfPresheaf PresheafOfνSet νSetRoundtrip.
From Bonak.νSet.Lib Require Import Equiv.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module PresheafRoundtrip (A: LayerSig).
Import A.

Module Export νSetRoundtrip := νSetRoundtrip.νSetRoundtrip A.

Section RoundTripGF.

Variable psh: Presheaf.

(** Aligning [g]'s synthesized chains with the presheaf-equipped ones

    [g]'s faces use chains synthesized at the [DepsCohs2] level
    ([chain2Down]); on candidate-built cells they must be recognized as
    images of chains of presheaf-equipped stages ([PshCohsChain]), so
    that [pshνFace] applies. *)

Definition PshPack {M P K} (PCTop: PshDepsCohs psh M P K): Type :=
  {p: nat &T {k: nat &T
    {PC: PshDepsCohs psh M p k &T PshCohsChain psh PCTop PC}}}.

Definition pshPackStep {M P K} {PCTop: PshDepsCohs psh M P K}
  (s: PshPack PCTop): PshPack PCTop :=
  (match s.1 as p0 return
     {k: nat &T {PC: PshDepsCohs psh M p0 k &T PshCohsChain psh PCTop PC}} ->
     PshPack PCTop with
   | 0 => fun s' => (0; s')
   | S p' => fun s' => (p'; (s'.1.+1; (proj1PshDepsCohs psh s'.2.1;
       PshCohsChainCons s'.2.2)))
   end) s.2.

Fixpoint pshChain2Down {M P K} (PCTop: PshDepsCohs psh M P K) (j: nat):
  PshPack PCTop :=
  match j with
  | 0 => (P; (K; (PCTop; PshCohsChainNil)))
  | S j => pshPackStep (pshChain2Down PCTop j)
  end.

Definition pshPackDC {M P K} {PCTop: PshDepsCohs psh M P K}
  (s: PshPack PCTop): DCPack (pshDepsCohs psh PCTop) :=
  (s.1; (s.2.1; (pshDepsCohs psh s.2.2.1; pshCohsChainCohs psh s.2.2.2))).

Lemma pshPackStepStage {M P K} {PCTop: PshDepsCohs psh M P K}
  (s: PshPack PCTop): (pshPackStep s).1 = Nat.pred s.1.
Proof.
  destruct s as (p, s2). now destruct p.
Qed.

Lemma pshChain2DownStage {M P K} (PCTop: PshDepsCohs psh M P K) (j: nat):
  (pshChain2Down PCTop j).1 = P - j.
Proof.
  induction j.
  - now rewrite sub0r.
  - now rewrite subSuccR, pshPackStepStage, IHj.
Qed.

Lemma pshPackDCStep {M P K} {PCTop: PshDepsCohs psh M P K}
  (s: PshPack PCTop): pshPackDC (pshPackStep s) = dcStep (pshPackDC s).
Proof.
  destruct s as (p, (k, (PC, C))). now destruct p.
Qed.

Lemma gfChainAlign {m} {Xpre: (νSetAt m.+1).(prefix)}
  (T: PshTower psh m Xpre) (rp: PshTowerRestrPaintings psh T) (j: nat):
  dc2PackDeps (chain2Down (νDepsCohs2At (pshNext psh m Xpre T rp)) j) =
  pshPackDC (pshChain2Down (towerPshDepsCohs psh T rp) j).
Proof.
  induction j.
  - now reflexivity.
  - now rewrite dc2PackDepsStep, IHj, pshPackDCStep.
Qed.

(** The face naturality at the bottom of the descent

    The face of a candidate-filled cell projects to the [psh]-face of its
    cell: align the chain, apply [pshνFace], fix the dimension. *)

Lemma gfFaceBottom {m} {Xpre: (νSetAt m.+1).(prefix)}
  (T: PshTower psh m Xpre) (rp: PshTowerRestrPaintings psh T)
  (dim: nat) (Hdim: dim <= m.+1) (ε: arity)
  (x: νTotal ((pshNext psh m Xpre T rp).(next _ _))):
  (νFaceFuel (pshNext psh m Xpre T rp) (m.+1 - dim) ε x).2.1 =
  psh.(Face) m.+1 dim Hdim ε x.2.1.
Proof.
  destruct x as (D, (d, e)).
  unfold νFaceFuel.
  rewrite e.
  rewrite (gfChainAlign T rp (m.+1 - dim)).
  assert (SE: (pshChain2Down (towerPshDepsCohs psh T rp) (m.+1 - dim)).1
    = dim).
  { rewrite pshChain2DownStage. now exact (subSubCancel Hdim). }
  rewrite (pshνFace psh
    ((pshChain2Down (towerPshDepsCohs psh T rp) (m.+1 - dim)).2.2.2)
    (leR_eq (eq_sym SE) Hdim) ε d).
  now exact (pshFaceDimIrr psh SE ε d).
Qed.

Lemma gfFaceBottom0 (dim: nat) (Hdim: dim <= 0) (ε: arity)
  (x: νTotal ((f psh).(next _ _))):
  (νFaceFuel (f psh) (0 - dim) ε x).2.1 = psh.(Face) 0 dim Hdim ε x.2.1.
Proof.
  destruct dim. 2: destruct (leR_O_contra Hdim).
  destruct x as (D, (d, e)).
  unfold νFaceFuel, νFace.
  rewrite e.
  now rewrite nth_lam.
Qed.

(** The levelwise equivalences and the naturality descent

    An explicit equation [L = n + m.+1] records the tower level reached
    after [n] relative steps from position [m.+1]. [natUIP] normalizes this
    equation at the base case, leaving the equivalences independent of
    transports along the descent. *)

Fixpoint gfEquiv {m} {Xpre: (νSetAt m.+1).(prefix)}
  (T: PshTower psh m Xpre) (rp: PshTowerRestrPaintings psh T)
  (n: nat) {struct n}:
  forall (L: nat), L = n + m.+1 ->
  Equiv (gF0 (pshNext psh m Xpre T rp) n) (psh.(F0) L) :=
  match n return forall (L: nat), L = n + m.+1 ->
    Equiv (gF0 (pshNext psh m Xpre T rp) n) (psh.(F0) L) with
  | 0 => fun L HL =>
      rew [fun l => Equiv (νTotal (pshNext psh m Xpre T rp)) (psh.(F0) l)]
        (eq_sym HL) in
      fillerEquiv (mkPshFrame psh (towerPshDeps psh T))
  | S n => fun L HL =>
      gfEquiv (towerStep psh T rp) (towerStepRestrPaintings psh T rp) n L
        (HL • plus_n_Sm n m.+1)
  end.

(** The threaded level equation is proof-irrelevant ([natUIP]), and the
    successor case of [gfEquiv] unfolds definitionally. These are the two
    facts used by the descent proofs on the folded fixpoint. *)

Lemma gfEquivIrr {m} {Xpre: (νSetAt m.+1).(prefix)}
  (T: PshTower psh m Xpre) (rp: PshTowerRestrPaintings psh T)
  (n L: nat) (HL HL': L = n + m.+1):
  gfEquiv T rp n L HL = gfEquiv T rp n L HL'.
Proof.
  now rewrite (natUIP HL HL').
Qed.

Fixpoint gfFaceEquiv {m} {Xpre: (νSetAt m.+1).(prefix)}
  (T: PshTower psh m Xpre) (rp: PshTowerRestrPaintings psh T)
  (n: nat) {struct n}:
  forall (L: nat) (HL: L = n + m.+1) (HL2: L.+1 = n.+1 + m.+1)
    (dim: nat) (Hd: dim <= n + m.+1) (Hd': dim <= L) (ε: arity)
    (x: gF0 (pshNext psh m Xpre T rp) n.+1),
  gfEquiv T rp n L HL
    (gFace (pshNext psh m Xpre T rp) n dim Hd ε x) =
  psh.(Face) L dim Hd' ε (gfEquiv T rp n.+1 L.+1 HL2 x).
Proof.
  destruct n; intros.
  - set (HLs := eq_sym HL).
    rewrite (natUIP HL (eq_sym HLs)).
    clearbody HLs. clear HL.
    destruct HLs.
    cbn [gfEquiv].
    rewrite (natUIP (HL2 • plus_n_Sm 0 m.+1) eq_refl).
    now exact (gfFaceBottom T rp dim Hd' ε x).
  - now exact (gfFaceEquiv _ _
      (towerStep psh T rp) (towerStepRestrPaintings psh T rp) n L
      (HL • plus_n_Sm n m.+1)
      (HL2 • plus_n_Sm n.+1 m.+1)
      dim (leR_eq_r (plus_n_Sm n m.+1) Hd) Hd' ε x).
Qed.

(** Assembly: the [g ∘ f] round trip *)

Definition gfF0Equiv (n: nat): Equiv (gF0 (f psh) n) (psh.(F0) n) :=
  match n with
  | 0 => fillerEquiv
      (B := mkFrame (toDepsRestr ((νSetAt 0).(data) tt).(restrFrames)))
      (fun _: psh.(F0) 0 => tt)
  | S n => gfEquiv (tower1 psh) (tower1RestrPaintings psh) n n.+1
      (f_equal S (plus_n_O n) • plus_n_Sm n 0)
  end.

Lemma gfFaceEquivTop (n q: nat) (Hq: q <= n) (ε: arity)
  (x: gF0 (f psh) n.+1):
  gfF0Equiv n ((g (f psh)).(Face) n q Hq ε x) =
  psh.(Face) n q Hq ε (gfF0Equiv n.+1 x).
Proof.
  destruct n.
  - unfold gfF0Equiv.
    rewrite (gfEquivIrr _ _ 0 _
      (f_equal S (plus_n_O 0) • plus_n_Sm 0 0) eq_refl).
    now exact (gfFaceBottom0 q Hq ε x).
  - now exact (gfFaceEquiv (tower1 psh) (tower1RestrPaintings psh) n n.+1
      (f_equal S (plus_n_O n) • plus_n_Sm n 0)
      (f_equal S (plus_n_O n.+1) • plus_n_Sm n.+1 0)
      q (leR_eq_r (f_equal S (plus_n_O n) • plus_n_Sm n 0) Hq)
      Hq ε x).
Qed.

Definition gf: PresheafEquiv (g (f psh)) psh :=
  Build_PresheafEquiv (g (f psh)) psh gfF0Equiv gfFaceEquivTop.

End RoundTripGF.

End PresheafRoundtrip.

Module PresheafRoundtripSimplicial := PresheafRoundtrip SimplicialLayer.
Module PresheafRoundtripCubical := PresheafRoundtrip CubicalLayer.
