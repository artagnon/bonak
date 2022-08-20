(** This file defines HSet and provides unit, sigT and forall on HSet *)

Require Import Logic.FunctionalExtensionality.
Require Import Logic.Eqdep_dec. (* UIP_refl_unit *)
Require Import Aux.

Set Universe Polymorphism.

Record HSet := {
  Dom:> Type;
  UIP {x y: Dom} {h g: x = y}: h = g;
}.

(** [unit] seen as an [HSet] *)

Lemma unit_UIP (x y: unit) (h g: x = y): h = g.
Proof.
  destruct g, x. now apply UIP_refl_unit.
Qed.

Lemma bool_UIP (x y: bool) (h g: x = y): h = g.
Proof.
  destruct g, x. all: now apply UIP_refl_bool.
Qed.

Definition hunit@{m}: HSet@{m} := {|
  Dom := unit;
  UIP := unit_UIP;
|}.

Definition hbool@{m}: HSet@{m} := {|
  Dom := bool;
  UIP := bool_UIP;
|}.

(** [sigT] seen as a type constructor on [HSet] *)

Lemma sigT_eq {A: Type} {B} {x y: {a: A & B a}}:
  (x.1; x.2) = (y.1; y.2) -> x = y.
Proof.
  now repeat rewrite <- sigT_eta.
Qed.

Lemma sigT_decompose_eq {A: Type} {B} {x y: {a: A & B a}} {p: x = y}:
  p = (sigT_eta x) • (= projT1_eq p; projT2_eq p) • (eq_sym (sigT_eta y)).
Proof.
  now destruct p, x.
Qed.

Lemma sigT_decompose {A: Type} {B} {x y: {a: A & B a}} {p q: x = y}
  {alpha: projT1_eq p = projT1_eq q}
  {beta: rew [fun r => rew [fun b: A => B b] r in x.2 = y.2] alpha in
   projT2_eq p = projT2_eq q}: p = q.
Proof.
  rewrite (sigT_decompose_eq (p := q)), (sigT_decompose_eq (p := p)).
  destruct x, y; simpl. now destruct beta, alpha.
Qed.

Lemma sigT_UIP {A: HSet} {B: A -> HSet} (x y: {a: A & B a}) (p q: x = y): p = q.
Proof.
  unshelve eapply sigT_decompose. now apply A. now apply (B y.1).
Qed.

Definition hsigT {A: HSet} (B: A -> HSet): HSet := {|
  Dom := {a: A & B a};
  UIP := sigT_UIP;
|}.

Set Warnings "-notation-overridden".

Notation "{ x & P }" := (hsigT (fun x => P)): type_scope.
Notation "{ x : A & P }" := (hsigT (A := A) (fun x => P)): type_scope.

(** [forall] defined over an [HSet] codomain *)

(* Bug! equal_f_dep is unnecessarily opaque in Coq *)
Lemma equal_f_dep: forall {A B} {f g: forall (x: A), B x},
  f = g -> forall x, f x = g x.
Proof.
  intros A B f g <- H; now reflexivity.
Defined.

Axiom fext_computes: forall {A: Type} {B: A -> HSet} {f: forall a: A, B a},
  functional_extensionality_dep f f (fun a: A => eq_refl) = eq_refl.

Lemma hpiT_decompose {A: Type} (B: A -> HSet)
  (f g: forall a: A, B a) (p: f = g):
  functional_extensionality_dep _ _ (equal_f_dep p) = p.
Proof.
  destruct p; simpl; now apply fext_computes.
Qed.

Definition hpiT_UIP {A: Type} (B: A -> HSet)
  (f g: forall a: A, B a) (p q: f = g): p = q.
Proof.
  rewrite <- hpiT_decompose with (p := p).
  rewrite <- hpiT_decompose with (p := q).
  f_equal.
  apply functional_extensionality_dep; intros a.
  apply (B a).
Qed.

Definition hpiT {A: Type} (B: A -> HSet): HSet.
Proof.
  exists (forall a: A, B a). intros x y h g. now apply hpiT_UIP.
Defined.

Notation "'hforall' x , A" := (hpiT (fun x => A))
(x binder, at level 200): type_scope.
