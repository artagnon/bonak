(** Univalence, and the equality of HSets it induces.

    Univalence is stated as [idToEquiv] being an equivalence; [ua] is its
    inverse, universe polymorphic so it applies both at the [Dom] level of HSets
    and one level up on ordinary types. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Stdlib Require Import Logic.FunctionalExtensionality.
From Bonak Require Import Notation HSet RewLemmas.
From Bonak.νSet.Lib Require Import Equiv.

Polymorphic Definition idToEquiv {A B: Type} (e: A = B): Equiv A B :=
  rew [Equiv A] e in idEquiv.

Polymorphic Axiom univalence: forall A B: Type, IsEquiv (@idToEquiv A B).

Polymorphic Definition uaEquiv (A B: Type): Equiv (A = B) (Equiv A B) :=
  {| eqvFun := @idToEquiv A B; eqvIsEquiv := univalence A B |}.

Polymorphic Definition ua {A B: Type} (e: Equiv A B): A = B := invEq (uaEquiv A B) e.

Polymorphic Lemma idToEquivRew {A B: Type} (e: A = B) (a: A):
  idToEquiv e a = rew [fun T: Type => T] e in a.
Proof.
  now destruct e.
Qed.

Polymorphic Lemma uaRew {A B: Type} (e: Equiv A B) (a: A):
  rew [fun T: Type => T] (ua e) in a = e a.
Proof.
  rewrite <- idToEquivRew.
  now exact (f_equal (fun E: Equiv A B => E a) (secEq (uaEquiv A B) e)).
Qed.

(** Equality of HSets from equivalence of their carriers.

    From univalence, [hsetEq] turns an equivalence of the carriers of two HSets
    into an equality of the HSets: the [Dom] path comes from univalence, and the
    [UIP] field is proof-irrelevant ([eq_hprop_UIP]); functional
    extensionality proves equality of the transported fields. *)

Definition hsetEqIntro (h1 h2: HSet) (p: h1.(Dom) = h2.(Dom)): h1 = h2.
Proof.
  destruct h1 as [d1 u1], h2 as [d2 u2]; cbn in p; destruct p.
  apply (f_equal (fun u => {| Dom := d1; UIP := u |})).
  apply functional_extensionality_dep_good; intro x.
  apply functional_extensionality_dep_good; intro y.
  apply functional_extensionality_dep_good; intro a.
  apply functional_extensionality_dep_good; intro b.
  now apply (eq_hprop_UIP (u1 x y)).
Defined.

Definition hsetEq {h1 h2: HSet} (e: Equiv h1 h2): h1 = h2 :=
  hsetEqIntro h1 h2 (ua e).

Lemma hsetEqIntroRew (h1 h2: HSet) (p: h1.(Dom) = h2.(Dom)) (x: h1):
  rew [Dom] (hsetEqIntro h1 h2 p) in x = rew [fun T: Type => T] p in x.
Proof.
  destruct h1 as [d1 u1], h2 as [d2 u2]; cbn in p; destruct p; cbn.
  rewrite <- (rew_map Dom (fun u => {| Dom := d1; UIP := u |})).
  now apply rew_const.
Qed.

Lemma hsetEqRew {h1 h2: HSet} (e: Equiv h1 h2) (x: h1):
  rew [Dom] (hsetEq e) in x = e x.
Proof.
  unfold hsetEq. rewrite hsetEqIntroRew. now apply uaRew.
Qed.

Lemma hsetEqRewSym {h1 h2: HSet} (e: Equiv h1 h2) (x: h2):
  rew [Dom] (eq_sym (hsetEq e)) in x = invEq e x.
Proof.
  apply (eqvInj e).
  now exact (eq_sym (hsetEqRew e _)
    • (rew_sym_cancel_r (P := Dom) (hsetEq e) x • eq_sym (secEq e x))).
Qed.
