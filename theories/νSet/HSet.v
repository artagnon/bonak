(** This file defines HSet and provides unit, sigT and forall on HSet *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.Eqdep_dec. (* UIP_refl_unit *)

Import EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT.

Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

Record HSet := {
  Dom:> Type;
  UIP {x y: Dom} {h g: x = y}: h = g;
}.

(** [unit] seen as an [HSet] *)

Lemma unit_UIP (x y: unit) (h g: x = y): h = g.
Proof.
  destruct g, x; now apply UIP_refl_unit.
Qed.

Lemma bool_UIP (x y: bool) (h g: x = y): h = g.
Proof.
  destruct g, x; now apply UIP_refl_bool.
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

Lemma sigT_eq {A: Type} {B} {x y: {a: A &T B a}}:
  (x.1; x.2) = (y.1; y.2) -> x = y.
Proof.
  now easy.
Qed.

Lemma sigT_decompose_eq {A: Type} {B} {x y: {a: A &T B a}} {p: x = y}:
  p = (= projT1_eq p; projT2_eq p).
Proof.
  now destruct p, x.
Qed.

Lemma sigT_decompose {A: Type} {B: A -> Type} {u v: {a: A &T B a}} {p q: u = v}
  {alpha: projT1_eq p = projT1_eq q}
  {beta: rew [fun r => rew [fun b: A => B b] r in u.2 = v.2] alpha in
   projT2_eq p = projT2_eq q}: p = q.
Proof.
  rewrite (sigT_decompose_eq (p := q)), (sigT_decompose_eq (p := p)).
  destruct u, v; simpl. now destruct beta, alpha.
Qed.

Lemma sigT_UIP {A: HSet} {B: A -> HSet} (x y: {a: A &T B a}) (p q: x = y):
  p = q.
Proof.
  unshelve eapply sigT_decompose. now apply A. now apply (B y.1).
Qed.

Definition hsigT {A: HSet} (B: A -> HSet): HSet := {|
  Dom := {a: A &T B a};
  UIP := sigT_UIP;
|}.

Set Warnings "-notation-overridden".

Notation "{ x & P }" := (hsigT (fun x => P%type)): type_scope.
Notation "{ x : A & P }" := (hsigT (A := A) (fun x => P%type)): type_scope.

(** [forall] defined over an [HSet] codomain *)

Lemma hpiT_decompose {A: Type} (B: A -> HSet)
  (f g: forall a: A, B a) (p: f = g):
  functional_extensionality_dep_good _ _
    (fun x => f_equal (fun H => H x) p) = p.
Proof.
  destruct p; now apply functional_extensionality_dep_good_refl.
Qed.

Definition hpiT_UIP {A: Type} (B: A -> HSet) (f g: forall a: A, B a)
  (p q: f = g): p = q.
Proof.
  rewrite <- hpiT_decompose with (p := p),
          <- hpiT_decompose with (p := q).
  f_equal.
  apply functional_extensionality_dep_good; intro a. now apply (B a).
Qed.

Definition hpiT {A: Type} (B: A -> HSet): HSet.
Proof.
  exists (forall a: A, B a). now apply hpiT_UIP.
Defined.

Notation "'hforall' x .. y , P" :=
  (hpiT (fun x => .. (hpiT (fun y => P%type)) ..))
  (at level 10, x binder, y binder, P at level 200,
  format "'[  ' '[  ' 'hforall'  x  ..  y ']' ,  '/' P ']'"): type_scope.
