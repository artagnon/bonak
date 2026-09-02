(** The equality theory of presheaves: the levelwise equivalence
    [PresheafEquiv], and its upgrade to an equality [presheafEquivEq].

    Two presheaves are the same when their cells correspond level by level,
    compatibly with the face maps. Univalence and functional extensionality are
    enough to turn such a correspondence into an equality. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak Require Import RewLemmas HSet LeSProp Notation νSet.Layer
  Funext Univalence Presheaf.
From Bonak.Lib Require Import Equiv.

Set Primitive Projections.
Set Printing Projections.
Set Keyed Unification.

Module PresheafEquiv (A: LayerSig).
Import A.

Module Export Psh := Presheaf.Presheaf A.

(** Equivalence of presheaves *)
Record PresheafEquiv (psh psh': Presheaf) := {
  F0Equiv n: Equiv (psh.(F0) n) (psh'.(F0) n);
  FaceEquiv n q (Hq: q <= n) (ε: arity) (X: psh.(F0) n.+1):
    F0Equiv n (psh.(Face) n q Hq ε X) =
    psh'.(Face) n q Hq ε (F0Equiv n.+1 X)
}.

(** Helper transport lemmas *)

Lemma rew_face_app {Ar: Type} {F01 F02: nat -> HSet} (e: F01 = F02)
  (h: forall n q (Hq: q <= n) (ε: Ar), F01 n.+1 -> F01 n)
  n q (Hq: q <= n) (ε: Ar) (Y: F02 n.+1):
  (rew [fun F0: nat -> HSet =>
     forall n q (Hq: q <= n) (ε: Ar), F0 n.+1 -> F0 n] e in h)
    n q Hq ε Y =
  rew [fun F0: nat -> HSet => (F0 n).(Dom)] e in
    (h n q Hq ε
      (rew [fun F0: nat -> HSet => (F0 n.+1).(Dom)] (eq_sym e) in Y)).
Proof.
  now destruct e.
Qed.

Lemma funExtBetaHSet {F01 F02: nat -> HSet} (H: forall n, F01 n = F02 n)
  (m: nat):
  f_equal (fun h: nat -> HSet => h m)
    (functional_extensionality_dep_good F01 F02 H) = H m.
Proof.
  now exact (f_equal__functional_extensionality_dep_good H m).
Qed.

(** Equality of presheaves

    An equality of presheaves reduces to an [F0] path, a transported
    [Face] path, and a [FaceCoh] path. [UIP] proves the last path, and
    [spropFunext] proves equality over the [SProp] bounds. *)

Lemma presheafEqIntro (psh1 psh2: Presheaf)
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

(** The transport is pushed inward until it becomes the equivalence. The
    [F0] path is [funext] of the levelwise HSet equalities ([hsetEq]);
    applying a transported face map computes through the function type
    ([rew_face_app]); the [F0] path then projects pointwise ([rew_map] +
    [funExtBetaHSet]); and transport along [hsetEq] is the equivalence
    ([hsetEqRew]). *)

Lemma presheafEquivEq {psh1 psh2: Presheaf} (E: PresheafEquiv psh1 psh2):
  psh1 = psh2.
Proof.
  apply (presheafEqIntro psh1 psh2
    (functional_extensionality_dep_good _ _
      (fun n => hsetEq (F0Equiv _ _ E n)))).
  apply functional_extensionality_dep_good; intro n.
  apply functional_extensionality_dep_good; intro q.
  apply spropFunext; intro Hq.
  apply functional_extensionality_dep_good; intro ε.
  apply functional_extensionality_dep_good; intro Y.
  rewrite rew_face_app.
  rewrite (rew_map (fun h: HSet => h.(Dom)) (fun F0: nat -> HSet => F0 n)).
  rewrite (rew_map (fun h: HSet => h.(Dom)) (fun F0: nat -> HSet => F0 n.+1)).
  rewrite <- eq_sym_f_equal.
  rewrite 2 funExtBetaHSet.
  cbv beta.
  rewrite hsetEqRew, hsetEqRewSym.
  refine (FaceEquiv _ _ E n q Hq ε (invEq (F0Equiv _ _ E n.+1) Y) • _).
  now exact (f_equal (psh2.(Face) n q Hq ε) (secEq (F0Equiv _ _ E n.+1) Y)).
Qed.

End PresheafEquiv.

Module PresheafEquivSimplicial := PresheafEquiv SimplicialLayer.
Module PresheafEquivCubical := PresheafEquiv CubicalLayer.
