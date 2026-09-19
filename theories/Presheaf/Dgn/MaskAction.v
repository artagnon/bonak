(** The action of coordinate-selection masks by iterated degeneracies. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet SigT Notation LeSProp NatLemmas.
From Bonak.Presheaf Require Import νSemiShape.
Require Export Bonak.Presheaf.Dgn.Presentation.
Set Primitive Projections.
Set Printing Projections.

Section MaskAction.
Context {A: HSet}.

Fixpoint applyMask (p: nat): forall k (d: Word hunit k p)
  (P: νSetPresentation A) (R: νDgnStructure P), P.(F0) k -> P.(F0) p.
Proof.
  destruct p as [|p]; intros k d P R x.
  - destruct k as [|k]; [exact x|destruct d].
  - destruct d as [[[] d]|d].
    + exact (R.(Dgn _) p p leR_refl (applyMask p k d P R x)).
    + destruct k as [|k]; [destruct d|].
      exact (applyMask p k d (shiftPresheaf P) (shiftDgn R) x).
Defined.

Arguments applyMask {p k} d {P} R x.

Lemma applyMaskId (p: nat): forall (P: νSetPresentation A) (R: νDgnStructure P) x,
  applyMask (wid p) R x = x.
Proof.
  induction p as [|p IH]; intros P R x; [reflexivity|].
  exact (IH (shiftPresheaf P) (shiftDgn R) x).
Qed.

Lemma applyMaskNatural (p: nat): forall k (d: Word hunit k p)
  (P Q: νSetPresentation A) (R: νDgnStructure P) (S: νDgnStructure Q)
  (T: forall n, P.(F0) n -> Q.(F0) n)
  (H: forall n q Hq x, T (Datatypes.S n) (R.(Dgn _) n q Hq x)
     = S.(Dgn _) n q Hq (T n x)) x,
  T p (applyMask d R x) = applyMask d S (T k x).
Proof.
  induction p as [|p IH]; intros k d P Q R S T H x.
  - destruct k as [|k]; [reflexivity|destruct d].
  - destruct d as [[[] d]|d].
    + cbn [applyMask]. rewrite H.
      exact (f_equal (S.(Dgn _) p p leR_refl) (IH k d P Q R S T H x)).
    + destruct k as [|k]; [destruct d|].
      exact (IH k d (shiftPresheaf P) (shiftPresheaf Q) (shiftDgn R) (shiftDgn S)
        (fun n => T (Datatypes.S n)) (fun n q Hq x => H (Datatypes.S n) q (↑ Hq) x) x).
Qed.

Definition topDgn {P: νSetPresentation A} (R: νDgnStructure P) n := R.(Dgn _) n n leR_refl.

Lemma applyMaskTopDgn {p k} (d: Word hunit k p)
  {P: νSetPresentation A} (R: νDgnStructure P) x:
  applyMask d (shiftDgn R) (topDgn R k x) = topDgn R p (applyMask d R x).
Proof.
  apply eq_sym.
  exact (applyMaskNatural p k d P (shiftPresheaf P) R (shiftDgn R)
    (topDgn R) (fun n q Hq x => eq_sym (R.(DgnDgn _) n q n Hq leR_refl x)) x).
Qed.

Lemma applyMaskTopFace {p k} (d: Word hunit k p)
  {P: νSetPresentation A} (R: νDgnStructure P) (a: A) x:
  P.(Face) p p leR_refl a (applyMask d (shiftDgn R) x)
  = applyMask d R (P.(Face) k k leR_refl a x).
Proof.
  exact (applyMaskNatural p k d (shiftPresheaf P) P (shiftDgn R) R
    (fun n => P.(Face) n n leR_refl a)
    (fun n q Hq x => R.(FaceDgnSup _) n n leR_refl q Hq a x) x).
Qed.

Lemma applyMaskComp (p: nat): forall m k (g: Word hunit m p) (f: Word hunit k m)
  (P: νSetPresentation A) (R: νDgnStructure P) x,
  applyMask (wcomp g f) R x = applyMask g R (applyMask f R x).
Proof.
  induction p as [|p IH]; intros m k g f P R x.
  - destruct m as [|m]; [destruct g; reflexivity|destruct g].
  - destruct g as [[[] g]|g].
    + cbn [wcomp applyMask wskip]. rewrite IH. reflexivity.
    + destruct m as [|m]; [destruct g|].
      destruct f as [[[] f]|f].
      * cbn [wcomp applyMask wskip].
        rewrite IH. exact (eq_sym (applyMaskTopDgn g R _)).
      * destruct k as [|k]; [destruct f|].
        exact (IH m k g f (shiftPresheaf P) (shiftDgn R) x).
Qed.

Lemma applyMaskGen (n: nat): forall q (Hq: q <= n)
  (P: νSetPresentation A) (R: νDgnStructure P) x,
  applyMask (wgen (A := hunit) n q tt) R x = R.(Dgn _) n q Hq x.
Proof.
  induction n as [|n IH]; intros q Hq P R x.
  - pose proof (leR0Eq Hq); subst q. reflexivity.
  - destruct (Nat.eqb q (S n)) eqn:E.
    + pose proof (natEqbEq _ _ E); subst q.
      rewrite wgenTop.
      change (R.(Dgn _) (S n) (S n) leR_refl (applyMask (wid (S n)) R x) = R.(Dgn _) (S n) (S n) Hq x).
      now rewrite applyMaskId.
    + pose proof (leRDown q n Hq E) as Hq'.
      rewrite (wgenLift Hq'). exact (IH q Hq' (shiftPresheaf P) (shiftDgn R) x).
Qed.

End MaskAction.
Arguments applyMask {A p k} d {P} R x.
