(** Face presentations equipped with cubical-style degeneracies. *)

Set Warnings "-notation-overridden".
From Bonak.Lib Require Import HSet Notation LeSProp SigT Funext.
From Stdlib Require Import Logic.FunctionalExtensionality.
Require Export Bonak.Presheaf.Presentation.
Set Primitive Projections.
Set Printing Projections.

Definition shiftPresheaf {A: HSet} (P: νSetPresentation A): νSetPresentation A := {|
  F0 n := P.(F0) (S n);
  Face n q Hq a := P.(Face) (S n) q (↑ Hq) a;
  FaceCoh n q Hq r Hr a b x := P.(FaceCoh) (S n) q (↑ Hq) r Hr a b x;
|}.

Definition shiftDgn {A: HSet} {P: νSetPresentation A} (R: νDgnStructure P):
  νDgnStructure (shiftPresheaf P) :=
  Build_νDgnStructure (shiftPresheaf P)
    (fun n q Hq => R.(Dgn _) (S n) q (↑ Hq))
    (fun n r q Hr Hq a x => R.(FaceDgnInf _) (S n) r q Hr (↑ Hq) a x)
    (fun n q Hq a x => R.(FaceDgnId _) (S n) q (↑ Hq) a x)
    (fun n q Hq r Hr a x => R.(FaceDgnSup _) (S n) q (↑ Hq) r Hr a x)
    (fun n r q Hr Hq x => R.(DgnDgn _) (S n) r q Hr (↑ Hq) x).

(** The levels, faces and degeneracies determine the complete presentation. *)

Lemma presheafDgnEq {arity: HSet} {psh: νSetPresentation arity} (R S: νDgnStructure psh)
  (e: R.(Dgn _) = S.(Dgn _)): R = S.
Proof.
  destruct R as [d ri rid rs rr], S as [d' si sid ss sr]; cbn in e.
  destruct e.
  f_equal;
    repeat first [apply functional_extensionality_dep_good; intro
                 |apply spropFunext; intro];
    apply (psh.(F0) _).(UIP).
Qed.

Lemma presheafWithDgnEq {arity: HSet} (X Y: νDgnSetPresentation arity)
  (e0: X.1.(F0) = Y.1.(F0))
  (ef: rew [fun F: nat -> HSet =>
         forall n i (Hi: i <= n) (ε: arity), F n.+1 -> F n] e0 in
       X.1.(Face) = Y.1.(Face))
  (ed: rew [fun F: nat -> HSet =>
         forall n i (Hi: i <= n), F n -> F n.+1] e0 in
       X.2.(Dgn _) = Y.2.(Dgn _)): X = Y.
Proof.
  destruct X as [[F f c] R], Y as [[F' f' c'] S]; cbn in e0, ef, ed.
  destruct e0; cbn in ef, ed. destruct ef.
  assert (ec: c = c').
  { repeat first [apply functional_extensionality_dep_good; intro
                 |apply spropFunext; intro].
    apply (F _).(UIP). }
  destruct ec.
  now destruct (presheafDgnEq R S ed).
Qed.
