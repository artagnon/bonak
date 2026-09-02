(** This file defines HGpd and provides unit and sigT on HGpd. *)

Import Logic.EqNotations.

Set Warnings "-notation-overridden".
From Bonak Require Import SigT HSet.

Set Primitive Projections.
Set Printing Projections.
Set Universe Polymorphism.

(** [HGpd] is the next truncation level: its identity types are [HSet]s. *)

Record HGpd := {
  GDom:> Type;
  GUIP {x y: GDom} {h g: x = y} {p q: h = g}: p = q;
}.

Definition hpaths {A: HGpd} (x y: A): HSet := {|
  Dom := x = y;
  UIP := @GUIP A x y;
|}.

Lemma retract_eq {A B: Type} (f: A -> B) (g: B -> A)
  (H: forall x, g (f x) = x) {x y: A} (p: x = y):
  p = eq_trans (eq_sym (H x)) (eq_trans (f_equal g (f_equal f p)) (H y)).
Proof.
  destruct p; simpl. destruct (H x). reflexivity.
Defined.

Lemma retract_UIP {A: Type} {B: HSet} (f: A -> B) (g: B -> A)
  (H: forall x, g (f x) = x) (x y: A) (p q: x = y): p = q.
Proof.
  rewrite (retract_eq f g H p).
  rewrite (retract_eq f g H q).
  now rewrite (@UIP B (f x) (f y) (f_equal f p) (f_equal f q)).
Defined.

(** A transparent copy of Stdlib's [Eqdep_dec.UIP_dec] (Hedberg's
    theorem): the stdlib proof chain is [Qed]-opaque, which would leave
    normal forms of groupoid-level coherences stuck on it. *)

Section EqdepDec.

Variable A: Type.

Let comp {x y y': A} (eq1: x = y) (eq2: x = y'): y = y' :=
  eq_ind _ (fun a => a = y') eq2 _ eq1.

Remark trans_sym_eq {x y: A} (u: x = y): comp u u = eq_refl y.
Proof.
  case u; trivial.
Defined.

Variable x: A.
Variable eq_dec: forall y: A, x = y \/ x <> y.

Let nu {y: A} (u: x = y): x = y :=
  match eq_dec y with
  | or_introl eqxy => eqxy
  | or_intror neqxy => False_ind _ (neqxy u)
  end.

#[local]
Lemma nu_constant {y: A} (u v: x = y): nu u = nu v.
Proof.
  unfold nu.
  destruct (eq_dec y) as [Heq|Hneq].
  - reflexivity.
  - case Hneq; trivial.
Defined.

Let nu_inv {y: A} (v: x = y): x = y := comp (nu (eq_refl x)) v.

Remark nu_left_inv_on {y: A} (u: x = y): nu_inv (nu u) = u.
Proof.
  case u; unfold nu_inv.
  apply trans_sym_eq.
Defined.

Theorem eq_proofs_unicity_on (y: A) (p1 p2: x = y): p1 = p2.
Proof.
  elim (nu_left_inv_on p1).
  elim (nu_left_inv_on p2).
  elim (nu_constant p1 p2).
  reflexivity.
Defined.

End EqdepDec.

Theorem UIP_dec (A: Type) (eq_dec: forall x y: A, {x = y} + {x <> y})
  (x y: A) (p1 p2: x = y): p1 = p2.
Proof.
  apply eq_proofs_unicity_on.
  intros y'; destruct (eq_dec x y'); [now left | now right].
Defined.

Lemma unit_GUIP (x y: unit) (h g: x = y) (p q: h = g): p = q.
Proof.
  apply UIP_dec. intros u v. left. now apply unit_UIP.
Defined.


Definition gunit@{m}: HGpd@{m} := {|
  GDom := unit;
  GUIP := unit_GUIP;
|}.


(** [sigT] seen as a type constructor on [HGpd] *)

Definition sigT_path_code {A: HGpd} {B: A -> HGpd} (x y: {a: A &T B a}):
  HSet :=
  hsigT (A := hpaths x.1 y.1)
    (fun p => hpaths (rew [B] p in x.2) y.2).

Definition sigT_path_encode {A: HGpd} {B: A -> HGpd} {x y: {a: A &T B a}}
  (p: x = y): sigT_path_code x y :=
  (projT1_eq p; projT2_eq p).

Definition sigT_path_decode {A: HGpd} {B: A -> HGpd} {x y: {a: A &T B a}}
  (p: sigT_path_code x y): x = y :=
  (= p.1; p.2).

Lemma sigT_path_decode_encode {A: HGpd} {B: A -> HGpd} {x y: {a: A &T B a}}
  (p: x = y): sigT_path_decode (sigT_path_encode p) = p.
Proof.
  symmetry. apply sigT_decompose_eq.
Defined.

Lemma sigT_GUIP {A: HGpd} {B: A -> HGpd} (x y: {a: A &T B a})
  (h g: x = y) (p q: h = g): p = q.
Proof.
  eapply retract_UIP with
    (f := @sigT_path_encode A B x y)
    (g := @sigT_path_decode A B x y).
  exact sigT_path_decode_encode.
Defined.

Definition gsigT {A: HGpd} (B: A -> HGpd): HGpd := {|
  GDom := {a: A &T B a};
  GUIP := sigT_GUIP;
|}.

Set Warnings "-notation-overridden".

Notation "{ x & P }" := (gsigT (fun x => P%type)): type_scope.
Notation "{ x : A & P }" := (gsigT (A := A) (fun x => P%type)): type_scope.
